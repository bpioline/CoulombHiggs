# CoulombHiggs
A Mathematica package for computing quiver invariants

The Mathematica package `CoulombHiggs.m` computes BPS indices of quiver quantum mechanics, i.e. the refined
Donaldson-Thomas invariants (specializations of the Hodge polynomial) of moduli spaces of semi-stable quiver
representations, for arbitrary dimension vectors and stability parameters. It implements and compares several
independent methods:
- the Higgs branch formula, based on Reineke's resolution of the Harder-Narasimhan recursion;
- the Coulomb branch formula, which expresses the index in terms of single-centered invariants and multi-centered
  black hole configurations;
- the flow tree and attractor tree formulae, which express it in terms of attractor indices;
- the Joyce formula and the Kontsevich-Soibelman wall-crossing formula;
- the Jeffrey-Kirwan residue formula for the Witten index, χ_y genus and elliptic genus, including framed invariants
  of toric quivers with potential computed from molten crystals.

It also provides tools for mutations, non-commutative Donaldson-Thomas invariants of brane tilings, the deformed
Denef equations for quivers with loops, and various utilities. The documentation `CoulombHiggs.pdf` describes all
routines of version 7.2, together with the optional add-on `CoulombHiggsFast.m`, which provides fast
implementations of the flow tree and Coulomb branch formulae (with compiled C++ programs for Coulomb indices with
many centres, in the folder `c/`) and a standalone Kontsevich-Soibelman wall-crossing routine. Installation
instructions for the add-on are given in the section "Fast routines" of the documentation.

## History

This project started in joint work with Jan Manschot and Ashoke Sen on the Coulomb branch formula for the
Poincaré-Laurent polynomial of the moduli space of stable quiver representations
[arXiv:1011.1258, 1103.1887, 1207.2230, 1302.5498, 1404.7154]. The first version of the package was released along
with [arXiv:1302.5498]. Version 2.0 [arXiv:1207.2230] added the Dolbeault polynomial, general single-centered
indices for basis vectors and generalized mutations; version 2.1 [arXiv:1404.7154] optimized the evaluation of
Coulomb indices; version 3.0 introduced an early version of the Jeffrey-Kirwan residue formula, made more robust in
version 5.0 [arXiv:1907.01354]. Version 4.0 [arXiv:1804.06928] introduced the flow tree formula, and version 6.0
[arXiv:2012.14358] the attractor tree formula, the Quiver Yangian algorithm for non-commutative DT invariants and
many tools for brane tilings. Version 6.2 [arXiv:2103.03205] added the computation of indices of Abelian quivers
from the deformed Denef equations. The various versions were uploaded to GitHub for the first time in December 2020.

Versions 7.0 to 7.2 are due to Léo Buisine ([Darkneew](https://github.com/Darkneew)), whom I warmly thank: they
implement the formulae of [arXiv:2106.02518] for D4- and D6-framed refined DT invariants of quivers with potential,
the Jeffrey-Kirwan residue formula for toric and framed quivers with residues enumerated by molten crystals and
evaluated block by block, and many fixes. The add-on `CoulombHiggsFast.m` and the C++ programs in `c/` were written in November 2026 with
[Claude Code](https://claude.com/claude-code), and checked against the original routines.

The package has been used by other authors, for instance in arXiv:1308.6829, 1603.01724, 2008.05432, 2011.04661,
2012.09769, 2101.01681.

The code can be used freely, but should be acknowledged if used for published results. Please send queries or bug
reports to pioline@lpthe.jussieu.fr
