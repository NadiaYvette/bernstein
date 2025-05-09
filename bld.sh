#!/bin/sh

CABAL=cabal-3.14.1.1
# The ghc version, keep-going: True and jobs: 256 are all already set in
# the cabal.project and it's not clear --preference=newer is a good idea.
# It may well be that none of ${CABAL_OPTS} should be there.
GHC=ghc-9.10.1
CABAL_OPTS="--keep-going --jobs=256 --with-compiler=${GHC} --preference=newer"

PKG=bernstein
SRC=./src/Numeric/Polynomial/Bernstein.lhs
LTX=./doc/Bernstein.ltx

ckret ()
{
	if [ $1 -ne 0 ]
	then
		exit $1
	fi
	return 0
}

export TEXINPUTS="$(pwd)/doc:"
export BIBINPUTS="$(pwd)/bib:"

# This is more for the sake of basic integrity checks than really trying
# to link the build process to anything. lhs2TeX needs a little help due
# to its age. Not that I'm getting any younger myself.
$CABAL $CABAL_OPTS build $PKG
ckret $?

# There are newer Haskell syntactic constructs that break lhs2TeX. I
# think it's the use of unpaired single quotes in quasiquoting or
# Template Haskell. I think it's known and those capable are preoccupied.
lhs2TeX $SRC -o $LTX
ckret $?

# The first pass of LaTeX generates the aux files bibtex/biber use to
# generate the bibliography.
pdflatex -output-directory ./doc/ $LTX
ckret $?
(cd doc; biber $(basename --suffix=.ltx $LTX))
ckret $?

# I'm not sure why it's 3 times vs. any other number. There's a list of
# things that can demand additional rerunnings to resolve labels or
# references or some such. What they are and how many of those can be
# stacked atop each other to demand more passes would be good to have an
# answer for and for just general knowledge.
# As it now stands, the third iteration of the for loop is redundant.
# However, there are things that can provoke needing a third pass after
# the bibtex/biber run. So keeping it up at 3 futureproofs a little.
for n in $(seq 1 3)
do
	pdflatex -output-directory ./doc/ $LTX
	ckret $?
done
