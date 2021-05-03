# CoulombHiggs
A mathematica package for computing quiver invariants

This project started in joint work with Jan Manschot and Ashoke Sen on the Coulomb branch formula for computing the Poincaré-Laurent polynomial of the moduli space of stable representations of quivers [1011.1258, 1103.1887, 1207.2230, 1302.5498,1309.7053]. The first version of the code was released along with [1302.5498] on arXiv. Since then it has been expanded in many directions, including the Reineke formula for quivers without relations, the Jeffrey-Kirwan residue formula, various versions of the flow tree formula, and most recently the Quiver Yangian algorithm for computing non-commutative DT invariants and various tools for dealing with brane tilings. See the documentation for more details. The various versions have been uploaded on Git for the first time in Dec 2020. This Git repository is not intended for collaborative use.

The code can be used freely, but should be acknowledged if used for published results. Please send queries or bug reports to pioline@lpthe.jussieu.fr 

History of changes:

 * Release notes for 2.0: 
 * - Removed argument y from CoulombBranchFormula, CoulombBranchFormulaFromH, 
 *   HiggsBranchFormula
 * - New recursion scheme for computing CoulombF, old one can be used by setting 
 *   $QuiverRecursion=1
 * - CoulombBranchFormula now computes the Dolbeault polynomial, as a function of the 
 *   single centered degeneracies OmS[gam,y,t]; This is done by using SwapFugacity in 
 *   the last step. The y argument is dropped by using DropFugacity.
 * - The assumption that basis vectors have OmS=1 (and multiples thereof have OmS=0) can
 *   be relaxed by setting $QuiverOmSbasis=0; 
 * - New routines MutateRight, MutateRightOmS, OmSToOmS2, etc for mutations have been introduced. Generalized mutations are 
 *   by setting $QuiverMutationMult>1
 * - CyclicQuiverOmS[Avec_,t_] computes the single-centered invariant associated to a 
 *   cyclic Abelian quiver with arrows Mat[i,i+1]=Avec[i]
 * - GrassmannianPoincare[k,n,y] gives the Poincare polynomial of the Grassmannian G(k,n)
 *
 * Release notes for 2.1: 
 * - Optimized CoulombF, CoulombG; old procedure can be recovered by setting $QuiverOpt=False.
 * - Relaxed condition that FI parameters sum up to zero
 *
 * Release notes for 2.2:
 * - Introduced StackInvariantGen, relaxing antisymmetry of DSZ matrix 
 * - Introduced EulerForm, SubVectors
 * - Introduced StackInvariantFast, computing StackInvariantGen using Reineke's fast algorithm
 * - Introduced HuaFormula
 *
 * Release notes for 3.0:
 * - Fixed bug in HuaFormula
 * - Introduced JKIndex, etc
 *
 * Release notes for 3.1:
 * - Introduced elliptic genus computation 
 * - beware, the intersection points on torus have not been implemented yet - see JeffreyKirwan8
 *
 * Release notes for 4.2:
 * - Introduced Tree Flow Formula
 *
 * Release notes for 4.3:
 * - Fixed bug in CompleteChargeMatrix, 
 * - added CompleteChargeNumMatrix, PartialChargeNumMatrix
 * - added DisplayFlagList, DisplaySingList, FindDegrees, FindStableDomains
 * - fixed bug in determining relevant flags from Euler index
 *
 * Release notes for 4.4:
 * - optimized the enumeration of stable flags
 * - removed JKIndex**SplitFromStableFlags, JKIndex**FromStableFlags, TestStableFlag
 *
 * Release notes for 4.5:
 * - Introduced SplitNodes argument in JKIndexSplit
 * - Introduced $QuiverNoVM, $QuiverTrig, JKListuDisplay, 
 * - Optimized ZRational, ZRationalPartial
 * - externalized JKInitialize from JKIndex, JKIndexSplit
 * - Allowed chemical potentials via R-charge Matrix
 * - replaced ZRational,ResidueRat by ZTrig, ResidueTrig in JKIndex, JKIndexSplit
 * - Added DisplayFlagTree, AbelianSubQuiver, FlavoredRMatrix
 * - Updated SubDSZ
 * - Fixed CyclicQuiverOmS, AttractorFI, ListLoopRCharges
 * - Optimized ExpandTheta
 *
 * Release notes for 5.0:
 * - Removed z variable in hyperplanes
 * - Renamed gEuler, gRat, gTrig, etc into ZEuler, ZRational, ZTrig
 * - Renamed IndEuler, IndHirzebruch into JKEuler, JKChiGenus
 * - Renamed ListRelevantStableFlags into JKRelevantStableFlags 
 * - Renamed InitializeJK into JKInitialize
 * - Renamed global variables ChargeMatrix, Etavec into JKChargeMatrix, JKEta
 * - Renamed Frozen* into JKFrozen*, Listu into Listu*, FlagVertex* into JKVertex*
 * - Renamed ListAll* into JKListAll*, EXCEPT ListAllPartitions
 * - Renamed JKResidueRat into JKResidueRational
 * - Added Joyce-Song formula
 *
 * Release notes for 5.1:
 * - Added Mutate
 * - Added $QuiverOnlyMultipleBasisVector, TestMultipleBasisVector
 * - Updated ListAllPartitions
 * - Optimized PlaneTreeSign
 * - Renamed $QuiverOpt to $QuiverCoulombOpt, added $QuiverFlowTreeOpt
 * - Added FlowTreeFormulaRat, BinarySplits, ToPrimitive,
 * - Added NonAbelianFlowTreeFormula, ListFirstWalls
 * - Added EvalReinekeIndex, ReinekeIndex
 * - Added EvalCoulombIndexAtt, MinimalModifFast, ReduceDSZMatrix, CompareDSZMatrices
 * - Fixed bug in FindSingularities, which occurred when ChargeMatrix is empty
 * - Changed RMat -> PMat in SubDSZ
 *
 * Release notes for 5.2:
 * - Redirected AbelianStackInvariant to StackInvariant
 * - Renamed JoyceSongFormula into JoyceFormula
 * - Renamed SubCvecABelian into SubFIAbelian, RandomCvec into RandomFI
 * - Added AttractorTreeFormula and related routines
 * - Added NCDTSeriesFromCrystal and routines
 * - Added CyclicQuiverDSZ, HiggsedDSZ, ConnectedQuiverQ
 * - Modified OmbToHiggsG and HiggsGToOmb to allow arbitrary stability
 * - Added GaugeMotive, DTSpectrumFromOmAtt, TrivialStackInvariant
 * - Added ListPerfectMatchings, ListKnownBraneTilings, PlotToricFan, PlotQuiver
 * - Added HeightMatrixToDSZ, HeightMatrixFromPotential
 *
 * Release notes for 6.0:
 * - Added QuiverMultiplierMat, $QuiverMultiplierAssumption
 * - Updated demo notebooks
 * 
 * Release notes for 6.1:
 * - Added TreeIndexOpt
 * - Removed PMat argument from TreeIndex
 * - Added D6Framing, D4Framing, CohomologicalWeight, CohomologicalSign, UnrefinedSeriesFromCrystal
 * - Merged ChargeFunction and VacuumChargeFunction
 * - Added data for Y30, Y31 
 * - Nmin and Nmax in NCDTSeriesFromOmAtt/OmS are now dimension vectors
 * - Added CyclicQuiverOmAtt,CyclicQuiverOmAttUnrefined,CyclicQuiverTrivialStacky 
 *  
 * Release notes for 6.2:
 * - Added ExtendedCoulombIndex, CoulombIndexResidue, FindCollinearSolutions
 * - Added ListClusters,  CoulombBranchFormulaNum,  CoulombBranchResidue
 

