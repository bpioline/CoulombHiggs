(* ::Package:: *)

(*********************************************************************
 *
 *  CoulombHiggs.m 6.0               
 *                                                          
 *  Copyright B. Pioline, Dec 2020
 *
 *  Distributed under the terms of the GNU General Public License 
 *
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
 * - Changed RMat \[Rule] PMat in SubDSZ
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
 
 *********************************************************************)
Print["CoulombHiggs 6.0 - A package for evaluating quiver invariants"];





BeginPackage["CoulombHiggs`"]

(** symbols **)

y::usage = "Angular momentum fugacity, conjugate to sum of Dolbeault degrees";

z::usage = "Angular momentum chemical potential, y=Exp[I Pi z]";

t::usage = "fugacity, conjugate to difference of Dolbeault degrees";

x::usage = "fugacity, conjugate to rank in Hua formula";

u::usage = "u[i,s]: s-th Cartan variable for i-th gauge group";

ut::usage = "ut[i]: Cartan variable u, rotated to the diagonal basis for flag";

Om::usage = "Om[gam_,y_] denotes the integer valued BPS index";

Omb::usage = "Omb[gam_,y_] denotes the rational BPS index";

OmT::usage = "OmT[gam_,y_] denotes the total single centered degeneracy with charge gam";

OmTRat::usage = "OmTRat[gam_,y_] gives the rational total invariant. Coincides with OmT[gam_,y_] if gam is primitive ";

OmS::usage = "OmS[gam_,y_,t_] denote the single centered degeneracy with charge gam. 
OmS[gam_,y_]=OmS[gam,y,1] is supposed to be y-independent, but the y-dependence must be retained till the end of the computation";

OmS2::usage = "OmS2[gam_,y_,t_] denote the single centered degeneracy with charge gam for 
mutated quiver ";

OmAtt::usage = "OmAtt[gam_,y_] denotes the attractor index with charge gam";

OmAttb::usage="OmAttb[gam_,y_] denotes the rational attractor index with charge gam";

Treeg::usage="Treeg[Li_,y_] denotes the tree index of n centers with charges Li";

HiggsG::usage = "HiggsG[gam_,y_] denotes the (unevaluated) stack invariant G_Higgs(gamma,y)";

Higgsg::usage = "Higgsg[gam_,y_] denotes the (unevaluated) Abelian stack invariant g_Higgs(gamma,y)";

Coulombg::usage = "Coulombg[Li_,y_] denotes the Coulomb index of n centers with charges Li";

CoulombH::usage = "CoulombH[Li_,Nvec_,y_] denotes the H-factor appearing in the formula for OmT[alpha_i] in terms of the single center degeneracies OmS[alpha_i,y]";

tau::usage = "tau denotes modulus of the elliptic curve";

q::usage = "q denotes Exp[2 Pi I tau]";

Theta::usage = "Theta[z_] represents the Jacobi Theta series Theta_1[z,tau]";

Eta::usage = "Eta represents the Dedekind eta function eta[tau]";

th::usage = "th[i_] denotes the i-th chemical potential for flavor symmetry";

h1::usage = "h1 denotes the first height parameter for brane tilings";

h2::usage = "h2 denotes the second height parameter for brane tilings";

h3::usage = "h3 denotes the third height parameter for brane tilings";

Phi::usage = "Phi[i,j,k] denotes the chiral field for the k-th arrow from i to j";


(* global variables *)

JKFrozenCartan::usage = "List of pairs {i,s} labelling frozen Cartan variables ";

JKFrozenRuleEuler::usage = "Rule for replacing the frozen u[i,s] by 0";

JKFrozenRuleRational::usage = "Rule for replacing the frozen u[i,s] by 1";

JKFrozenMask::usage = "Vector of booleans indicating non-frozen entries in JKListuAll ";

JKListu::usage = "List of non-frozen Cartan variables u[i,s] ";

JKListut::usage = "List of rotated Cartan variables ut[i]";

JKListuAll::usage = "List of all u[i,s] variables ";

JKListuDisplay::usage = "List of all u[i,s] variables, in Display mode ";

JKListAllPerms::usage = "List of partitions at each node (represented by a standard permutation) and corresponding multiplicity ";

JKListAllSings::usage= "Keeps track of singular hyperplanes for all permutations ";

JKListAllStableFlags::usage="Keeps track of stable flags for all permutations ";

JKChargeMatrix::usage = "ChargeMatrix is the matrix of gauge charges, R-charges and multiplicities for chiral multiplets";

JKEta::usage = "Extended stability vector, perturbation from diagonal embedding of Cvec "; 

JKRelevantStableFlags::usage = "List of stable flags contributing to the Euler number, as computed by JKIndex or JKIndexSplit";

JKEuler::usage = "List of contributions of all stable flags to the Euler number, as computed by JKIndex or JKIndexSplit";

JKChiGenus::usage = "List of contributions of all stable flags to the chi-genus, as computed by JKIndex or JKIndexSplit";

JKVertexCoordinates::usage = "Coordinates of vertices for DisplayFlagTree";

JKVertexLabels::usage = "Labels of vertices for DisplayFlagTree";

BraneTilingsData::usage = "List of {name, Fan, hMat, Wp, Wm, v1, v2} for known brane tilings"; 



(** environment variables variables **)

$QuiverPerturb1::usage = "Inverse size of beta1 perturbation, default =1000";

$QuiverPerturb2::usage = "Inverse size of beta2 perturbation, default =100000";

$QuiverPrecision::usage = "Precision to decide vanishing, default=0";

$QuiverNoLoop::usage = "Default=False, set to True if quiver can be assumed to have no scaling solutions ";

$QuiverTestLoop::usage = "Default=True, set to False to disable removal of CoulombH and OmS associated to non-scaling subquivers. Irrelevant if $QuiverNoLoop=True ";

$QuiverVerbose::usage = "Default=True, set to False to skip data consistency tests and messages ";

$QuiverMultiplier::usage = "Overall multiplier of DSZ matrix, default=1, could be matrix-valued";

$QuiverMultiplierAssumption::usage = "Specifies assumptions about entries in $QuiverMultiplier";

$QuiverDisplayCoulombH::usage = "Default=False, set to True in order that CoulombBranchFormula returns both Poincare polynomial and replacement rules for CoulombH ";

$QuiverRecursion::usage = "Default=1, set to 0 to use the old recursion scheme for CoulombF ";

$QuiverOmSbasis::usage = "Default=1, set to 0 to relax the assumption that OmS=1 for basis vectors, OmS=0 for multiples thereof ";

$QuiverMutationMult::usage = "Default=1, set to M>1 for generalized quiver mutations ";

$QuiverCoulombOpt::usage = "Default=1, set to 0 for old unoptimized evaluation of gCoulomb";

$QuiverFlowTreeOpt::usage = "Default=0, set to 1 or 2 for alternate evaluation of gTree";

$QuiverFlowTreeMethod::usage = "Default=0, set to 1 for using CoulombIndex in NonAbelianFlowTreeFormula";

$QuiverNoVM::usage = "Default=False, set to True to ignore vector multiplet poles in JKIndex and JKIndexSplit";

$QuiverTrig::usage = "Default=False, set to True to use trigonometric variables in JKIndex and JKIndexSplit";

$QuiverMaxPower::usage = "Maximal power in the q-expansion of the elliptic genus, set to k=0 initially ";
 
$QuiverOnlyMultipleBasisVector::usage = "If true, then ListAllPartitions will produce partitions involving only multiple of basis vectors";
  
$QuiverDisplayCrystal::usage ="If True, then NCDTSeriesFromCrystal[hMat_,Framing_,Nn_] will produce a list of {Generating function, List of crystals with Nn atoms}";  

$QuiverVertexLabels::usage = "Specify the vertex labels to be used by PlotQuiver and PlotTiling";
  
(** Coulomb index computations **)

CoulombF::usage = "CoulombF[Mat_, Cvec_] returns the index of collinear solutions with DSZ products Mat, FI terms Cvec and trivial ordering.";

CoulombG::usage = "CoulombG[Mat_] returns the index of scaling collinear solutions with DSZ products Mat and trivial ordering. The total angular momentum Sum[Mat[i,j],j>i] must vanish ";

CoulombIndex::usage = "CoulombIndex[Mat_,PMat_,Cvec_,y_] returns the Coulomb index for n centers with DSZ products Mat, perturbed to PMat to lift accidental degeneracies, FI terms Cvec, angular momentum fugacity y ";

CoulombFOpt::usage = "CoulombFOpt[Mat_, Cvec_] returns the index of collinear solutions with DSZ products Mat, FI terms Cvec and trivial ordering.";

CoulombGOpt::usage = "CoulombGOpt[Mat_] returns the index of scaling collinear solutions with DSZ products Mat and trivial ordering. The total angular momentum Sum[Mat[i,j],j>i] must vanish ";

CoulombIndexOpt::usage = "CoulombIndexOpt[Mat_,PMat_,Cvec_,y_] returns the Coulomb index for n centers with DSZ products Mat, perturbed to PMat to lift accidental degeneracies, FI terms Cvec, angular momentum fugacity y ";

CoulombIndexNum::usage = "CoulombIndexNum[Mat_,PMat_,Cvec_,y_] returns the Coulomb index for n centers with DSZ products Mat, perturbed to PMat to lift accidental degeneracies,  FI terms Cvec, angular momentum fugacity y, computed numerically. Not for more than 6 centers.";

CoulombTestOrdering::usage = "CoulombTestOrdering[Mat_,Cvec_,Li_] looks numerically for collinear solutions of Coulomb problem with DSZ matrix Mat, FI terms Cvec, and ordering Li (a permutation of Range[Length[Mat]]). Not for more than 5 centers.";

CoulombFNum::usage = "CoulombFNum[Mat_,Cvec_] computes numerically the index F of collinear solutions,assuming DSZ matrix Mat and FI terms Cvec. Not for more than 5 centers.";

CoulombGNum::usage = "CoulombGNum[Mat_] computes numerically the index G of scaling collinear solutions,assuming DSZ matrix Mat. The total angular momentum Sum[Mat[i,j],j>i] must vanish. Not for more than 6 centers.";

EvalCoulombIndex::usage="EvalCoulombIndex[Mat_,PMat_,Cvec_,f_] evaluates the Coulomb indices Coulombg[{alpha_i}] appearing in g using DSZ matrix Mat, deformed to PMat, rescaled by $QuiverMultiplicity, and FI terms Cvec";

EvalCoulombIndexAtt::usage="EvalCoulombIndexAtt[Mat_,PMat_,f_] evaluates the Coulomb indices Coulombg[{alpha_i}] appearing in g using DSZ matrix Mat, deformed to PMat, rescaled by $QuiverMultiplicity, in the respective attractor chamber computed from PMat";

EvalCoulombIndexNum::usage="EvalCoulombIndex[Mat_,PMat_,Cvec_,f_] evaluates the Coulomb indices Coulombg[{alpha_i}] appearing in g using DSZ matrix Mat, deformed to PMat, rescaled by $QuiverMultiplicity, and FI terms Cvec, using numerical search ";

(** Coulomb branch formula **)

CoulombBranchFormula::usage = "CoulombBranchFormula[Mat_,Cvec_,Nvec_] expresses the Dolbeault polynomial of a quiver with dimension vector gam in terms of the single center degeneracies OmS[alpha_i,t] using the Coulomb branch formula, computing all CoulombH factors recursively using the minimal modification hypothesis. Also provides list of CoulombH factors if $QuiverDisplayCoulombH is set to True ";

CoulombBranchFormulaFromH::usage = "CoulombBranchFormulaFromH[Mat_,Cvec_,Nvec_,R_] expresses the Dolbeault polynomial of a quiver with dimension vector gam in terms of the single center degeneracies OmS[alpha_i,y] using the Coulomb branch formula, using CoulombH factors provided in replacement rule R ";

QuiverPoincarePolynomial::usage = "QuiverPoincarePolynomial[gam_,y_] expresses the Dolbeault polynomial of a quiver with dimension vector gam in terms of the total single center degeneracies OmT[alpha_i,y] and Coulomb indices Coulombg[{alpha_i},y]. If gam is primitive, QuiverPoincarePolynomial[gam] coincides with QuiverPoincarePolynomialRat[gam_].";

QuiverPoincarePolynomialRat::usage = "QuiverPoincarePolynomialRat[gam_,y_] expresses the rational Dolbeault polynomial of a quiver with dimension vector gam in terms of the total single center degeneracies OmT[alpha_i,y] and Coulomb indices Coulombg[{alpha_i},y]";

QuiverPoincarePolynomialExpand::usage ="QuiverPoincarePolynomialExpand[Mat_,PMat_,Cvec_,Nvec_,Q_]evaluates the Coulomb indices Coulombg[{alpha_i}] and expresses the total single center degeneracies OmT[alpha_i,y] in terms of the single center degeneracies OmS[alpha_i,y] and the CoulombH factors inside the Poincare polynomial Q ";

ListCoulombH::usage = "ListCoulombH[Nvec_,Q_] returns a pair {ListH,ListC} where ListH is a list of CoulombH factors possibly appearing in the Poincare polynomial Q of a quiver with dimension vector  Nvec, and ListC is the list of coefficients which multiply the monomials in OmS[alpha_i,y] canonically associated to the CoulombH factors in Q. ";

SolveCoulombH::usage = "SolveCoulombH[ListH_,ListC_,soH_] returns a list of replacement rules for the CoulombH factors in ListH, applying the minimal modification hypothesis to the corresponding coefficient in ListC. The last argument soH is a replacement rule for CoulombH factors associated to subquivers. ";

(** Higgs branch formula **)

HiggsBranchFormula::usage = "HiggsBranchFormula[Mat_,Cvec_,Nvec_] computes the Poincare polynomial of a quiver with DSZ matrix Mat, FI parameters Cvec, dimension vector Nvec using Reineke's formula. Accurate only for quivers without closed loops.";

StackInvariant::usage = "StackInvariant[Mat_,Cvec_,Nvec_,y_] gives the stack invariant of a quiver with DSZ matrix Mat, dimension vector Nvec and FI parameters Cvec computed using Reineke's formula ";

StackInvariantGen::usage = "StackInvariantGen[Mat_,Cvec_,Nvec_,y_] gives the stack invariant of a quiver with exchange matrix Mat, dimension vector Nvec and FI parameters Cvec computed using Reineke's formula ";

StackInvariantFast::usage = "StackInvariantFast[Mat_,Cvec_,Nvec_,y_] gives the stack invariant of a quiver with exchange matrix Mat, dimension vector Nvec and FI parameters Cvec computed using Reineke's fast algorithm ";

AbelianStackInvariant::usage = "AbelianStackInvariant[Mat_,Cvec_,y_] gives the Abelian stack invariant of a quiver with DSZ matrix Mat and FI parameters Cvec computed using Reineke's formula ";

QFact::usage = "QFact[n_,y_] represents the unevaluated q-deformed Factorial ";

QDeformedFactorial::usage = "QDeformedFactorial[n_,y_] gives the q-deformed factorial ";

EvalQFact::usage = "EvalQFact[f_] replaces QFact[n_,y_] with QDeformedFactorial[n,y] everywhere in f ";

EulerForm::usage = "EulerForm[Mat] gives the Euler form constructed from the DSZ matrix Mat ";

(* mutations *)
Mutate::usage = "MutateRight[Mat_,klist_] mutates the quiver with respect to nodes in klist ";

MutateRight::usage = "MutateRight[Mat_,Cvec_,Nvec_,klist_] mutates the quiver with respect to nodes in klist ";

MutateLeft::usage = "MutateLeft[Mat_,Cvec_,Nvec_,klist_] mutates the quiver with respect to nodes in klist ";

OmSToOmS2::usage = "OmSToOmS2[f_] replaces OmS[gam,...] by OmS2[gam,...] everywhere in f ";

MutateRightOmS::usage = "MutateRightOmS[Mat_,k_,f_] replaces every OmS[gam] by OmS2[gam'] where gam'=gam+max(0,<gam,gam_k>) gam_k, except when gam is collinear with gam_k ";

MutateRightOmS2::usage = "MutateRightOmS2[Mat_,k_,f_] replaces every OmS2[gam] by OmS[gam'] where gam'=gam+max(0,<gam,gam_k>) gam_k, except when gam is collinear with gam_k ";

MutateLeftOmS::usage = "MutateLeftOmS[Mat_,k_,f_] replaces every OmS[gam] by OmS2[gam'] where gam'=gam+max(0,-<gam,gam_k>) gam_k, except when gam is collinear with gam_k ";

MutateLeftOmS2::usage = "MutateLeftOmS2[Mat_,k_,f_] replaces every OmS2[gam] by OmS[gam'] where gam'=gam+max(0,-<gam,gam_k>) gam_k, except when gam is collinear with gam_k ";

DropOmSNeg::usage = "DropOmSNeg[f_] replaces every OmS[gam] and OmS2[gam] by zero any time gam contains a negative entry ";

CompareDSZMatrices::usage = "CompareDSZMatrices[Mat1_,Mat2_] gives a list of permutations P such that Mat1=Mat2[[P,P]], if they exist"; 

(* Hua formula *)

HuaFormula::usage = "HuaFormula[Mat_,Nvec_] computes the generating function of A-polynomials with dimensions up to Nvec ";

PartitionWeight::usage="PartitionWeight[pa_]computes the weight of a partition in Hua's formula ";

PartitionPairing::usage="PartitionPairing[pa1_,pa2_] computes the pairing between two partitions ";

AllPartitions::usage="AllPartitions[d_] constructs all partitions with entries less than d ";

HuaTermMult::usage="HuaTermMult[Mat_,ListPa_] computes the contribution of one set of partitions to Hua's formula ";

(* Jeffrey-Kirwan residue formula *)

JKIndex::usage = "JKIndex[ChargeMatrix_,Nvec_,Etavec_] computes the chi_y genus of the GLSM with given charge matrix, dimension vector and stability parameter ";

JKIndexSplit::usage = "JKIndexSplit[ChargeMatrix_,Nvec_,Etavec_,SplitNodes_] computes the chi_y genus of the GLSM with given charge matrix, dimension vector and stability parameter, using Cauchy's formula for the nodes listed in SplitNodes ";

JKInitialize::usage = "JKInitialize[Mat_,RMat_,Cvec_,Nvec] initializes the internal variables "; 

ZEuler::usage="ZEuler[ChargeMatrix,Nvec] computes the integrand in the residue formula for the index ";
 
ZRational::usage= "ZRational[ChargeMatrix,Nvec] constructs the integrand in the residue formula for the chi_y genus in rational representation ";

ZTrig::usage= "ZTrig[ChargeMatrix,Nvec] constructs the integrand in the residue formula for the chi_y genus in trigonometric representation ";

ZElliptic::usage= "ZElliptic[ChargeMatrix,Nvec] constructs the integrand in the residue formula for the elliptic genus ";

ZEulerPartial::usage="ZEulerPartial[ChargeMatrix,Nvec,ListPerm] constructs the partial contribution to the integrand in the residue formula for the index, corresponding to the partitions Listperm at each node; the sum over all permutations reproduces ZEuler[ChargeMatrix,Nvec]";

ZRationalPartial::usage= "ZRationalPartial[ChargeMatrix_,Nvec_,ListPerm_] constructs the partial contribution to the integrand in the residue formula for the chi_y genus in rational representation, corresponding to the partitions Listperm at each node; ; the sum over all permutations reproduces ZRational[ChargeMatrix,Nvec]";

ZTrigPartial::usage="ZTrigPartial[ChargeMatrix,Nvec,ListPerm] constructs the partial contribution to the integrand in the residue formula for the chi_y genus in trigonometric representation, corresponding to the partitions Listperm at each node; the sum over all permutations reproduces ZTrig[ChargeMatrix,Nvec]";

ZEllipticPartial::usage="ZEllipticPartial[ChargeMatrix,Nvec,ListPerm] constructs the partial contribution to the integrand in the residue formula for the elliptic genus, corresponding to the partitions Listperm at each node; the sum over all permutations reproduces ZTrig[ChargeMatrix,Nvec]";

JKResidueRational::usage= "JKResidueRational[Flags_,f_] extracts the sum of the residues of f (in rational representation) at the specified Flags, weighted with sign; the first entry in Flags is the intersection point, the second is a list of r-plets of charges for each flag ";  

JKResidueTrig::usage ="JKResidueTrig[Flags_,f_] extracts the sum of the residues of f (in trigonometric representation) at the specified Flags, weighted with sign; the first entry in Flags is the intersection point, the second is a list of r-plets of charges for each flag ";  

FindSingularities::usage = "FindSingularities[ChargeMatrix_] constructs the list of singular hyperplanes for the specified charge matrix ";

FindStableFlags::usage = "FindStableFlags[Inter_,ListHyper_,Nvec_,Etavec_] constructs the list of stable flags with stability parameter Etavec from the specified intersection and list of singular hyperplanes ";

FindStableDomains::usage = "FindStableDomains[Inter_,ListHyper_,Nvec_,Etavec_] gives the stability conditions for each flag at given singularity ";

ExpandTheta::usage = "ExpandTheta[f_] replaces Theta[z] and Eta by its Fourier expansion up to order q^$QuiverMaxPower, using both q and tau variables ";

qSeries::usage = "qSeries[f_] computes the Fourier expansion of f[q,tau] up to order q^$QuiverMaxPower";

DisplayFlagList::usage = "DisplayFlagList[ListFlags_,ListDegrees_] displays the list of list of (intersection point, stable flag, sign, degree)";

DisplaySingList::usage = "DisplaySingList[ListSings_] displays the list of list of (intersection point, intersecting hyperplanes, projective test)";

DisplayFlagListDegrees::usage = "DisplayFlagListDegrees[ListSings_,ListFlags_,NumSing_] displays the list of list of (intersection point, stable flag, sign, multidegree)";

FindMultiDegree::usage = "FindMultiDegree[ListSings_,NumSing_,Inter_,StableFlag_]";

DisplayFlagTree::usage = "DisplayFlagTree[f_] displays flag f as a spanning tree";

FlavoredRMatrix::usage= "FlavoredRMatrix[Mat_] constructs the matrix of R charges with generic flavor potentials, assuming no oriented loops";

(* Flow tree formula *)

FlowTreeFormula::usage = "FlowTreeFormula[Mat_,Cvec_,Nvec_] computes the index of a quiver with DSZ matrix Mat, stability parameters Cvec and dimension vector Nvec in terms of attractor indices";

FlowTreeFormulaRat::usage = "FlowTreeFormulaRat[Mat_,Cvec_,Nvec_] computes the rational index of a quiver with DSZ matrix Mat, stability parameters Cvec and dimension vector Nvec in terms of rational attractor indices";

TreePoincarePolynomialRat::usage = "TreePoincarePolynomialRat[gam_,y_] expresses the rational BPS index in terms of terms of attractor indices and tree index ";

EvalTreeIndex::usage="EvalTreeIndex[Mat_,PMat_,Cvec_,f_] evaluates any Treeg[Li,y] appearing in f using TreeIndex[] with arguments computed from the full DSZ matrix Mat, its perturbation PMat and the stability parameters Cvec ";

TreeF::usage="TreeF[Mat_,Cvec_] computes the partial tree index by summing over stable planar trees using PlaneTreeSign[]";

PlaneTreeSign::"PlaneTreeSign[Mat_,Cvec_,Li_] computes the contribution to the partial tree index from the grouping Li recursively ";

TreeIndex::"TreeIndex[Mat_,PMat_,Cvec_,y_] computes the tree index by summing all partial tree indices computed using TreeF[]";

TreeFAlt1::usage="TreeFAlt1[Mat_,Cvec_] computes the partial tree index by summing over stable planar trees using the first alternative recursion ";

TreeFAlt2::usage="TreeFAlt2[Mat_,Cvec_] computes the partial tree index by summing over stable planar trees using the second alternative recursion ";

TreeFAlt1Att::usage="TreeFAlt1Att[Mat_] computes  the attractor contribution to the partial tree index appearing in the first alternative recursion ";

TreeFAlt2Att::usage="TreeFAlt2Att[Mat_] computes  the attractor contribution to the partial tree index appearing in the second alternative recursion ";

PlaneTreeSplitList::usage="PlaneTreeSplitList[n_] constructs all splittings of Range[1,n] appearing in the alternative recursions for the partial tree index ";

DSZProdAbelian::usage="DSZProdAbelian[Mat_,Li1_,Li2_] computes the DSZ product for two vectors labelled by list of vertices ";

SubDSZAbelian::usage="SubDSZAbelian[Mat_,Li_] computes the DSZ matrix for the subquiver labelled by a list of vertices ";

SubCvecAbelian::usage="SubCvecAbelian[Cvec_,Li_] is obsolete, use SubFIAbelian instead";

SubFIAbelian::usage="SubFIAbelian[Cvec_,Li_] computes the stability parameters $c_i$ for the subquiver labelled by a list of vertices ";

NonAbelianFlowTreeFormula::usage="NonAbelianFlowTreeFormula[Mat_,Cvec_,Nvec_] expresses the rational invariant in terms of rational tree invariants using the non-Abelian flow tree formula"; 

ListFirstWalls::usage="ListFirstWalls[Mat_,Cvec_,Nvec_] gives a list of {{gamL,nL},{gam,nR}} corresponding to the walls encountered in the attractor flow from Cvec";

EvalReinekeIndex::usage="EvalReinekeIndex[Mat_,Cvec_,f_] evaluates all Coulombg factors in f using Reineke's formula for Abelian stack invariants";

ReinekeIndex::usage="ReinekeIndex[Mat_,Cvec_,y_] computes the Abelian stack invariant after perturbing Cvec";

(* Attractor tree formula *)

AttractorTreeFormula::usage="AttractorTreeFormula[Mat_,Cvec_,Nvec_] computes the index of a quiver with DSZ matrix Mat, stability parameters Cvec and dimension vector Nvec in terms of attractor indices.";

AttractorTreeFormulaRat::usage="AttractorTreeFormulaRat[Mat_,Cvec_,Nvec_] computes the rational index of a quiver with DSZ matrix Mat, stability parameters Cvec and dimension vector Nvec in terms of rational; attractor indices.";

AttractorIndex::usage="AttractorIndex::usage[Mat_,Cvec_,y_] evaluates the Attractor index as a sum over rooted trees with valency greater or equal to 3.";

EvalAttractorIndex::usage="EvalAttractorIndex[Mat_,Cvec_,f_]evaluates any Treeg[Li_,y_] appearing in f using AttractorIndex.";

AttractorF::usage="AttractorF:[ListVertices_,Mat_,Cvec_] computes the partial Attractor index by summing over rooted planar trees; the first argument supplies the list of vertices in each tree, computed by AttractorTreeVertices ";

Attractorg::usage="Attractorg[Mat_,Cvec_] computes the sign factor assigned to a given vertex in a Attractor tree, with Sign[0]^m replaced by 1/(m+1) if m even, or 0 if m odd ";

AttractorTreeList::usage="AttractorTreeList[n_] constructs the list of rooted planar trees with valency greater or equal to 3, represented as groupings of {1,..,n}";

AttractorTreeVertices::usage="AttractorTreeVertices[t_] constructs the list of {vertex, { children}} in the rooted planar tree t, the last one in the list being for the root vertex.";

AttractorTreeTriples::usage="AttractorTreeTriples[t_] constructs the list of {left vertex, right vertex, parent} in the rooted planar tree t.";

SimplifyOmAttbasis::usage="SimplifyOmAttbasis[f_] replaces OmAtt[gam_,y_] by 1 if gam is a basis vector, or 0 if gam is a multiple of a basis vector.";



(* for Jeffrey-Kirwan residue formula *)
ChargeMatrixFromQuiver::usage = "ChargeMatrixFromQuiver[Mat_,RMat_,Nvec_] constructs the charge matrix for a quiver with DSZ matrix Mat, R-charge matrix RMat, and dimension vector Nvec; do not forget to set JKFrozenCartan={{1,1}} to decouple the overall U(1)";

CompleteChargeMatrix::usage= "CompleteChargeMatrix[ChargeMatrix_,Nvec_] constructs the extended charge matrix consisting of chiral multiplets and vector multiplets ";

PartialChargeMatrix::usage= "PartialChargeMatrix[ChargeMatrix_,Nvec_,perm_] constructs the extended charge matrix consisting of chiral multiplets and vector multiplet contributions associated to the permutations perm ";

CompleteChargeNumMatrix::usage= "CompleteChargeNumMatrix[ChargeMatrix_,Nvec_] constructs the extended numerator charge matrix consisting of chiral multiplets and vector multiplets ";

PartialChargeNumMatrix::usage= "PartialChargeNumMatrix[ChargeMatrix_,Nvec_,perm_] constructs the extended numerator charge matrix consisting of chiral multiplets and vector multiplet contributions associated to the permutations perm ";

SameFlagQ::usage= "SameFlagQ[Q1_,Q2_] tests if the flags Q1 and Q2 (represented by square charge matrices) are equivalent ";

LegCharge::usage= "LegCharge[Nvec_,{i_,ii_},{j_,jj_}] constructs a charge vector with 1 in position {i,ii} and -1 in position {j,jj}";

TrimChargeTable::usage= "TrimChargeTable[ChargeMatrix_] removes the last two columns and frozen entries in charge matrix ChargeMatrix ";

FindIntersection::usage="FindIntersection[Sing_] computes the intersection points of the hyperplanes listed in Sing on the cylinder ";

FindDegrees::usage="FindDegrees[ListSings_,NumSing_] computes the degrees at the various intersection points ";

FlagToHyperplanes::usage = "FlagToHyperplanes[Sing_] translates the flag Sing, given as r-plet of charge vectors, into a list of linear combinations of Cartan variables ";

PartitionToPermutation::usage = "PartitionToPermutation[pa_] translates the partition pa into a standard permutation ";

PermutationToPartition::usage = "PermutationToPartition[perm_] translates the standard permutation perm into a partition ";

PartitionMultiplicity::usage="PartitionMultiplicity[pa_]";

ListPermutationsWithMultiplicity::usage = "ListPermutationsWithMultiplicity[Nvec_] computes the list of all multi-partitions of Nvec, represented by a standard permutation, and their multiplicity ";

ListHyperplanesIntersectingAt::usage = "ListHyperplanesIntersectingAt[ListSings_,Inter_] collects all the hyperplanes in ListSings which intersect at Inter ";

TestProjectiveIntersection::usage = "TestProjectiveIntersection[ListSings_,Inter_] tests if the intersection point Inter of the hyperplanes listed in ListSings is projective ";

CollectHyperplanes::usage = "CollectHyperplanes[ListInterrplets_,Inter_] collects all the hyperplanes from ListInterrplets, which intersect at the point Inter ";

TestStableFlag::usage = "TestStableFlag[ListHyper_,Flag_,Etavec_] tests if the flag Flag constructed out of the hyperplanes in ListHyper is stable with respect to Etavec ";

ResidueFast::usage = "ResidueFast[f_,{x_,x0_}] computes the residue of f at x=x0, without simplifying the result";

(* for Joyce formula *)

JoyceSongFormula::usage="JoyceSongFormula is obsolete, please use JoyceFormula instead"; 

JoyceFormula::usage="JoyceFormula[Mat_,Cvec1_,Cvec2_,f_] replaces all Omb[gam,y] and HiggsG[gam,y] in f, all assumed to refer to stability Cvec1, with their corresponding values at Cvec2, using the Joyce-Song formula";

JoyceIndex::usage="JoyceIndex[Mat_,Li_,Cvec1_,Cvec2_,y_] computes the index gJoyce appearing in the Joyce-Song formula";

JoyceIndexAlt::usage="JoyceIndexAlt[Mat_,Li_,Cvec1_,Cvec2_,y_] computes the index gJoyce appearing in the Joyce-Song formula for y->1, generalized naively to y<>1;";

SFactor::usage="SFactor[Li_,Cvec1_,Cvec2_] computes the factor S appearing in the definition of gJoyce";

UFactor::usage="UFactor[al_,Cvec1_,Cvec2_] computes the factor U appearing in the definition of gJoyce";

LFactor::usage="LFactor[Mat_,Li_,y_] computes the factor L appearing in the Joyce-Song formula as y->1";

Slope::usage="Slope[Nvec_,Cvec_] computes the slope Sum[Nvec[i]Cvec[i]]/Sum[Nvec[i]] ";

GaugeMotive::usage="GaugeMotive[Nvec_,y_] computes the motive of gauge group Prod_i GL[Nvec[[i]]]";

DTSpectrumFromOmAtt::usage="DTSpectrumFromOmAtt[Mat_,Cvec_,Nvec_] computes all rational invariants with dimension vector less or equal to Nvec; the result is a list of replacement rules Omb[gam_,y_]:> (result)";

TrivialStackInvariant::usage="TrivialStackInvariant[Mat_,Cvec_,Nvec_] computes the stack invariant for trivial stability condition, in terms of the rational invariants Omb[gam,y] for stability Cvec";


(* for framed invariants *)

NCDTSeriesFromOmS::usage="NCDTSeriesFromOmS[Mat_, Framing_, Nmin_,Nmax_] constructs the gener- ating function of NCDT invariants for the quiver with DSZ matrix Mat and framing Framing using the Coulomb branch formula, for dimension vectors with height from Nmin up to NMax.";

NCDTSeriesFromOmAtt::usage="NCDTSeriesFromOmAtt[Mat_, Framing_, Nmin_,Nmax_] constructs the gen- erating function of NCDT invariants for the quiver with DSZ matrix Mat and framing Framing using the Flow Tree formula, for dimension vectors with height from Nmin up to NMax.";

NCDTSeriesFromCrystal::usage="NCDTSeriesFromCrystal[hMat_, Framing_,Nmax_] constructs the generating function of NCDT invariants for the quiver with height matrix hMat and framing Framing using the Quiver Yangian algorithm, for dimension vectors with height up to NMax.";

FramedDSZ::usage="FramedDSZ[Mat_,Framing_] constructs the DSZ matrix of the framed quiver obtained by attaching arrows from the framing node (labelled 0) to the node i of the original quiver with DSZ matrix Mat.";

FramedFI::usage="FramedFI[Nvec_]constructs a random FI parameter for a framed quiver with dimension vector [1; Nvec], with first entry much larger than the other ones.";

BondFactor::usage="BondFactor[hMat_,i_,j_,z_] evaluates the bond factor \[CurlyPhi]^{i->j(z), where hMat is a matrix whose (i, j)-entry is the list of heights of the arrows from node i to node j. The heights are in turn linear combinations of parameters h1, h2, h3";

ChargeFunction::usage="[ChargeFunction[hMat_,Framing_,Crys_,i_,z_] constructs the charge function Phi^i_C(z) for the molten crystal C = Crys. The crystal is encoded in a list of {color, height} for each atom.";

VacuumChargeFunction::usage="VacuumChargeFunction[Framing_,i_,z_] provides the chargefunction Phi^i_0(z)= 1 + Framing[i]/z for the full crystal. Can be redefined to accommodate non-standard vacuum charge functions.";

AddToCrystal::usage="AddToCrystal[hMat_,Framing_,i_,Crys_]constructs the list of molten crystals obtained by attaching one atom of color i to the molten crystal Crys.";

GrowCrystalList::usage="GrowCrystalList[hMat_,Framing_,CrysList_] constructs the molten crystals obtained from the list Crysli by attaching one additional atom of any color, or none at all";

CrystalDim::usage="CrystalDim[r_,Crys_] computes the dimension vector for the crystal Crys, assuming that the colors can take values 1 up to r";

EulerNorm::usage="EulerNorm[hMat_,Nvec_] computes the Ringel-Tits norm of the dimension vector Nvec from the matrix of heights hMat";

PlotTiling::usage="PlotTiling[hMat_,Nn_,v_,Range_,Shor_,Perf_] produces a 2D plot of the brane tiling defined by the matrix hMat, by iterating the arrows Nn times, removing those which belong to the perfect matching Perf. v is a list of 2D vectors {v1,v2} determining the vector v=x1 v1+x2 v2 associated to an arrow with weight x1 h1 +x2 h2 +x3 h3. The plot range is set to Range, and arrows are shortened by Shor. If the argument Perf is omitted, all arrows are included";

PlotTiling3D::usage="PlotTiling3D[hMat_,Nn_,v_,Range_,Perf_] produces a 3D plot of the brane tiling defined by the matrix hMat, by iterating the arrows Nn times, removing those which belong to the perfect matching Perf. v is a list of 3D vectors {v1,v2,v3} determining the vector v=x1 v1+x2 v2+x3 v3 associated to an arrow with weight x1 h1 +x2 h2 +x3 h3. The plot range is set to Range. If the argument Perf is omitted, all arrows are included";

PlotToricFan::usage="PlotToricFan[Fan_] produces a 2D plot of the polygon with vertices listed in Fan";

ListPerfectMatchings::usage="ListPerfectMatchings[Wp_,Wm_] produces the list of cuts for the potential Wp-Wm; each term in the potential must be a sum of monomials in Phi[i,j,k] with unit coefficient, and each perfect matching is represented by a list of triplets {i,j,k}";

PlethysticExp::usage="PlethysticExp[f_,Nn_] computes the plethystic exponential of f, assuming that it is a function of x[i] and y only";

PlethysticLog::usage="PlethysticLog[f_,Nn_] computes the plethystic logarythm of f , assuming that it is a function of x[i] and y only";

ListKnownBraneTilings::usage ="ListKnownBraneTilings lists the names known brane tilings. The data for each can be extracted from the global variable BraneTilingsData";


(** Utilities **)

SymmetryFactor::usage = "SymmetryFactor[pa_] gives 1/|Aut| where Aut is the subgroup of the permutation group leaving the list pa invariant ";

ListAllPartitions::usage = "ListAllPartitions[gam_] returns the list of unordered partitions of the positive integer vector gam as a sum of positive integer vectors "; 

ListAllPartitionsMult::usage = "ListAllPartitionsMult[gam_] returns the list of unordered partitions of the positive integer vector gam as a sum of positive integer vectors with multiplicities "; 

ListSubQuivers::usage = "ListSubQuivers[Nvec_] gives a list of all dimension vectors less or equal to Nvec ";

SimplifyOmSbasis::usage = "SimplifyOmSbasis[f_] replaces OmS[gam,y]->1 when gam is a basis vector ";

SimplifyOmSmultbasis::usage = "SimplifyOmSmultbasis[f_] replaces OmS[gam,y]->0 if gam is a non-trivial multiple of a basis vector ";

SwapFugacity::usage = "Replaces OmS[Nvec_,y^m_] by OmS[Nvec,y^m,t^m]";

DropFugacity::usage = "Replaces OmS[Nvec_,y_] and OmS[Nvec_,y_,t_] by OmS[Nvec]";

EvalCoulombH3::usage = "EvalCoulombH3[Mat_,f_] evaluates any 3-center CoulombH factor in f.";

TestNoLoop::usage = "TestNoLoop[Mat_,Li_] tests if the quiver made from vectors in list Li is a tree ";

TestNoFullLoop::usage = "TestNoFullLoop[Mat_,Li_] tests if the quiver made from vectors in list Li has no loop going through all nodes ";

CoulombHNoLoopToZero::usage = "CoulombHNoLoopToZero[Mat_,f_] sets to zero any CoulombH factor in f corresponding to non-scaling subquivers. Returns f is $QuiverTestLoop=False.";

OmTNoLoopToZero::usage = "OmTNoLoopToZero[Mat_,f_]sets to zero any OmT in f corresponding to non-scaling subquivers (except basis vectors). Returns f is $QuiverTestLoop=False.";

OmSNoLoopToZero::usage = "OmSNoLoopToZero[Mat_,f_]sets to zero any OmS in f corresponding to non-scaling subquivers (except basis vectors). Returns f is $QuiverTestLoop=False.";

OmAttNoLoopToZero::usage = "OmAttNoLoopToZero[Mat_,f_]sets to zero any OmAtt in f corresponding to non-scaling subquivers (except basis vectors). Returns f is $QuiverTestLoop=False.";

OmTToOmS::usage="OmTToOmS[f_] expands any OmT in f into sums of products of CoulombH and OmS factors ";

SubDSZ::usage = "SubDSZ[Mat_,PMat_,Cvec_,Li_] gives the DSZ matrix, perturbed DSZ matrix and FI parameters of the subquiver made of vectors in list Li ";

AbelianSubQuiver::usage = "AbelianSubQuiver[Mat_,RMat_,Cvec_,Nvec_,perm_]gives the DSZ matrix, R-charge matrix and FI parameters of the subquiver associated to the list of permutations perm";

MinimalModif::usage = "MinimalModif[f_] returns the symmetric Laurent polynomial which coincides with the Laurent expansion expansion of the symmetric rational function f at y=0, up to strictly positive powers of y. Here symmetric means invariant under y->1/y.";

MinimalModifFast::usage = "MinimalModifFast[f_] returns the symmetric Laurent polynomial which coincides with the Laurent expansion expansion of the symmetric rational function f at y=0, up to strictly positive powers of y. This assumes that the order of the pole at y=0 is manifest.";

OmToOmb::usage = "OmToOmb[f_] expresses any Om[gam,y] in f in terms of Omb[gam,y]";

OmbToOm::usage = "OmbToOm[f_] expresses any Omb[gam,y] in f in terms of Om[gam,y]";

OmAttToOmAttb::usage = "OmAttToOmAttb[f_] expresses any OmAtt[gam,y] in f in terms of OmAttb[gam,y]";

OmAttbToOmAtt::usage = "OmAttbToOmAtt[f_] expresses any OmAttb[gam,y] in f in terms of OmAtt[gam,y]";

StackInvariantToOmb::usage = "StackInvariantToOmb[gam_,y_] expresses the stack invariant GHiggs[gam,y] in terms of sums of products of Omb; Coincides with Omb[gam,y] if charge vector is primitive ";

HiggsGToOmb::usage = "HiggsGToOmb[f_] expresses any HiggsG[gam,y] in f in terms of Omb[gam,y]";

OmbToHiggsG::usage = "OmbToHiggsG[f_] expresses any Omb[gam,y] in f in terms of HiggsG[gam,y]";

EvalHiggsg::usage = "EvalHiggsg[Mat_,Cvec_,f_] evaluates any Higgsg[Li,y] appearing in f using Reineke's formula for Abelian quivers ";

EvalHiggsG::usage = "EvalHiggsG[Mat_,Cvec_,f_] evaluates any HiggsG[gam,y] appearing in f using Reineke's formula ";

EvalHiggsGGen::usage = "EvalHiggsG[Mat_,Cvec_,f_] evaluates any HiggsG[gam,y] appearing in f using Reineke's formula ";

CoulombHSubQuivers::usage = "CoulombHSubQuivers[Mat_,PMat_,Nvec_,y_] computes all CoulombH factors for dimension vector strictly less than Nvec ";

RandomCvec::usage = "RandomCvec[gam_] is obsolete, use RandomFI instead";

RandomFI::usage = "RandomFI[gam_] generates a random set of FI parameters between -1 and 1";


UnitStepWarn::usage = "UnitStepWarn[x_] gives 1 for x>0, 0 for x<0, and produces a warning for x=0";
UnitStepWarn::zero = "UnitStep with vanishing argument, evaluates to 1/2";

AttractorFI::usage = "AttractorFI[Mat_,Nvec_] gives the attractor stability condition";

FIFromZ::usage = "FIFromZ[Nvec_,Zvec_] computes the FI parameters from dimension vector Nvec and central charge vector Zvec ";

QuiverPlot::usage = "QuiverPlot[Mat_] displays the quiver with DSZ matrix Mat (obsolete, use PlotQuiver instead)";

PlotQuiver::usage = "PlotQuiver[Mat_] displays the quiver with DSZ matrix or height matrix Mat ";

HirzebruchR::usage = "HirzebruchR[J_,v_] is the function R_v(J) entering in the Hirzebruch-Riemann-Roch formula ";

GrassmannianPoincare::usage = "GrassmannianPoincare[k_,n_,y_] gives the Poincar\[EAcute] polynomial of the Grassmannian G(k,n)";

CyclicQuiverOmS::usage = "CyclicQuiverOmS[Vec_,t_] gives the single-centered degeneracy associated to a cyclic quiver with Vec arrows (assuming Vec[[i]]>0)";

CyclicQuiverDSZ::usage = "CyclicQuiverDSZ[avec_] constructs the DSZ matrix for a cyclic quiver with avec[[i]] arrows from node i to node i+1";

EulerForm::usage = "EulerForm[Mat_] gives the Ringel-Tits form ";

SubVectors::usage = "SubVectors[Nvec_] gives a list of dimension vectors strictly less than Nvec ";

ListLoopRCharges::usage = "ListLoopRCharges[Mat_,RMat_] computes the R-charge of the primitive loops in a quiver with DSZ matrix Mat ";

RandomDSZWithNoLoop::usage = "RandomDSZWithNoLoop[n_,$QuiverMaxPower_] generates a random antisymmetric nxn matrix with off-diagonal entries less than $QuiverMaxPower in absolute value, ensuring that the quiver has no loop ";

RandomDSZWithLoop::usage = "RandomDSZWithNoLoop[n_,$QuiverMaxPower_] generates a random antisymmetric nxn matrix with off-diagonal entries less than $QuiverMaxPower in absolute value, ensuring that the quiver has one loop or more ";

TestMultipleBasisVector::usage = "TestMultipleBasisVector[Li_] gives True if all elements of Li are multiples of basis vectors";
PartitionToInvervals::usage="PartitionToInvervals[pa_] turn an integer partition of length l into intervals 0<a_1<...<a_l";

DSZProd::usage="DSZProd[Mat_,Nvec1_,Nvec2_] computes the inner product Sum[Nvec1[i]Nvec2[j]Mat[i,j]";

DSZkappa::usage = "DSZkappa[m_,y_] returns(y^m-y^(-m))/(y-1/y)";

BinarySplits::usage="BinarySplits[Nvec_] gives the list of dimension vectors which are smaller than Nvec/2";

ToPrimitive::usage="ToPrimitive[Nvec_] gives {gam,d} where d=GCD[Nvec] and gam=Nvec/d";

CodeToLabeledTreeAlt::usage = "CodeToLabeledTreeAlt[li_] constructs the labelled tree with Prufer code li";

ReduceDSZMatrix::usage="ReduceDSZMatrix[Mat_,Li_] returns the matrix obtained from Mat by setting  Mat[[i, j]] = Mat[[j, i]] = 0 for all elements {i, j} in Li. If i = j, then the i-th row and column of Mat are set to 0.";

HiggsedDSZ::usage="HiggsedDSZ[Mat_,i_,j_]constructs the DSZ matrix of the quiver obtained from the quiver with DSZ matrix Mat by merging the node j with the node i";

ConnectedQuiverQ::usage="ConnectedQuiverQ[Mat_,Nvec_] returns True is the restriction of the quiver with DSZ matrix Mat to the nodes where Nvec has non-trivial support is connected";

HeightMatrixToDSZ::usage="HeightToDSZ[hMat_] computes the skew-symmetric Euler form from the matrix of heights";

HeightMatrixFromPotential::usage="HeightMatrixFromPotential[Wp_,Wm_,{i1_,j1_,k1_},{i2_,j2_,k2_}] construct the matrix of heights such that the arrow Phi[i1,j1,k1] has height h1, the arrow Phi[i2,j2,k2] has height h2 and all monomials in the potential W=Wp-Wm have height h3";

QuiverMultiplierMat::usage="QuiverMultiplierMat[i_,j_] gives the multiplier to be applied to the (i,j) entry of the DSZ matrix, constructed from $QuiverMultiplier";
 


Begin["`Private`"]

$QuiverPerturb1=50;
$QuiverPerturb2=50*50*1000; 
$QuiverPrecision=0;
$QuiverNoLoop=False;
$QuiverTestLoop=True;
$QuiverVerbose=True;
$QuiverMultiplier=1;
$QuiverMultiplierAssumption=True;
$QuiverDisplayCoulombH=False;
$QuiverRecursion=1;
$QuiverOmSbasis=1;
$QuiverMutationMult=1;
$QuiverCoulombOpt=1;
$QuiverFlowTreeOpt=0;
$QuiverNoVM=False;
$QuiverTrig=False;
$QuiverMaxPower=0;
$QuiverOnlyMultipleBasisVector=False;
$QuiverFlowTreeMethod=True;
$QuiverDisplayCrystal=False;
$QuiverVertexLabels={};



(* ::Section:: *)
(*Coulomb index *)


(* compute incidence matrix and FI terms for collapsed configuration *)
MatRedC[Mat_,Cvec_,li_]:=Module[{li2=Select[li,Length[#]>0&]},
	{Table[Sum[Mat[[li2[[i,k]],li2[[j,l]]]],{k,Length[li2[[i]]]},{l,Length[li2[[j]]]}],
		{i,Length[li2]},{j,Length[li2]}],
	 Table[Sum[Cvec[[li2[[i,k]]]],{k,Length[li2[[i]]]}],{i,Length[li2]}]
}];

MatRed[Mat_,li_]:=Module[{li2=Select[li,Length[#]>0&]},
	Table[Sum[Mat[[li2[[i,k]],li2[[j,l]]]],{k,Length[li2[[i]]]},{l,Length[li2[[j]]]}],
	{i,Length[li2]},{j,Length[li2]}]];

(* lambda deformation for computing F *)
Matlambda[Mat_,l_]:=Table[If[Abs[i-j]>1,l Mat[[i,j]],Mat[[i,j]]],{i,Length[Mat]},{j,Length[Mat]}];

(* mu deformation for computing G *)
Matmu[Mat_,mu_]:=Table[
   Which[
  i==Length[Mat],mu Mat[[i,j]],
  j==Length[Mat], mu Mat[[i,j]],
  (i==Length[Mat]-3)&&(j==Length[Mat]-1),
      Mat[[i,j]]+(1-mu) Sum[Mat[[k,Length[Mat]]],{k,Length[Mat]-1}],
  (i==Length[Mat]-1)&&(j==Length[Mat]-3),
      Mat[[i,j]]-(1-mu) Sum[Mat[[k,Length[Mat]]],{k,Length[Mat]-1}],
  True, Mat[[i,j]]],{i,Length[Mat]},{j,Length[Mat]}];
 
(* lambda for computing F new *)
 la[Mat_, k_] := (-Sum[
                       Sum[Mat[[s, j]], {j, s + 1, Length[Mat]-1}], {s, k + 1,
                           Length[Mat] - 2}]/
                  Sum[Mat[[s, Length[Mat]]], {s, k + 1,
    Length[Mat] -1}]);

 (* new FI for computing F new *)
 CNewF[Cvec_, k_] := Flatten[{Take[Cvec, {1, k}], Sum[Cvec[[i]], {i, k+1, Length[Cvec]}]}];
 
 (* deformed DSZ matrix for F for computing F new *)
 MNewF[Mat_, k_] :=
 Flatten[{Table[Flatten[{Take[Mat, {i, i}, {1, k}],
    Sum[Mat[[i, j]], {j, k + 1, Length[Mat] - 1}] +
    Mat[[i, Length[Mat]]] la[Mat,k] }], {i, 1, k}],
    {Flatten[{Table[-(Sum[Mat[[i, j]], {j, k + 1, Length[Mat] - 1}]
                      + Mat[[i, Length[Mat]]] la[Mat,k]), {i,1,k}], 0}]}}, 1];
 
(* deformed DSZ matrix for G for computing F new *)
 
 MNewG[Mat_, k_] :=
 Flatten[{Table[Flatten[{Take[Mat, {i, i}, {k+1, Length[Mat]-1}],
    la[Mat,k] Mat[[i, Length[Mat]]]}], {i, k+1, Length[Mat]-1}],
    {Flatten[{Table[-(la[Mat,k] Mat[[i, Length[Mat]]]), {i,k+1, Length[Mat]-1}], 0}]}}, 1];
 
 
 


CoulombIndex[Mat_,PMat_,Cvec_,y_]:=Module[{m,ListPerm,i,j,k,RMat,RCvec},
	m=Length[Cvec];
	If[$QuiverVerbose,
		If[Max[Flatten[PMat-Mat]]>1/2,Print["CoulombIndex: PMat is not close to Mat !"]];
        If[Abs[Plus@@Cvec]>$QuiverPrecision,Print["CoulombIndex: CVec does not sum to zero !"]];
	];
	ListPerm=Permutations[Range[m]];
    Do[ If[Abs[Sum[Cvec[[ListPerm[[j,i]]]],{i,k}]]<=$QuiverPrecision, 
           If[Abs[Sum[Mat[[ListPerm[[j,i1]],ListPerm[[j,i2]]]],
                {i1,k},{i2,k+1,m}]]>$QuiverPrecision,
               Print["CoulombIndex: FI sit on wall of marginal stability"];Break[]];
          ],{k,1,IntegerPart[m/2]},{j,Length[ListPerm]}
    ];
	(* RMat is a further eps_ 2 perturbation *)
	RMat=Table[Random[Integer,{1,100000}],{i,m},{j,m}];
	RMat=1/100000/$QuiverPerturb2 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,m},{j,m}];
	RCvec=1/1000/$QuiverPerturb2 Table[Random[Integer,{1,1000}],{i,m}];
	RCvec[[m]]=-Sum[RCvec[[i]],{i,m-1}];
	If[$QuiverVerbose,PrintTemporary["CoulombIndex: evaluating for ",m," centers"]];
	(y-1/y)^(1-m) (-1)^(Sum[QuiverMultiplierMat[i,j] Mat[[i,j]],{i,Length[Cvec]},{j,i+1,m}]+m-1)
	   Sum[y^( Sum[QuiverMultiplierMat[ListPerm[[k,i]],ListPerm[[k,j]]] Mat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,i+1,m}])
		CoulombF[Table[PMat[[ListPerm[[k,i]],ListPerm[[k,j]]]]+
					   RMat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,m}],
                 Table[Cvec[[ListPerm[[k,i]]]]+RCvec[[ListPerm[[k,i]]]],{i,m}]],
       {k,Length[ListPerm]}]
];

(* induction rule for F *)
CoulombF[Mat_,Cvec_]:= Which[
$QuiverRecursion==0,
Module[{m=Length[Mat]},
  If[$QuiverVerbose,
    If[Length[Cvec]!=m,Print["CoulombF: Length of DSZ matrix and FI vector do not match !"]];
    If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["CoulombF: DSZ matrix is not antisymmetric !"]];
    If[Abs[Plus@@Cvec]>$QuiverPrecision,
		Print["CoulombF: FI terms do not sum up to zero !"]];
    If[Min[Table[If[l-k+1<Length[Cvec],Abs[Sum[Cvec[[i]],{i,k,l}]],1],
			{k,1,m},{l,k,m}]]<=$QuiverPrecision,
		Print["CoulombF: FI sit on wall of marginal stability"]];
    If[Min[Table[Abs[Mat[[i,i+1]]],{i,m-1}]]<=$QuiverPrecision,
		Print["CoulombF: Some alpha(i,i+1) vanishes !"]];
    If[Min[Table[Min[Abs[Sum[Mat[[i,i+1]],{i,k,l-1}]],Abs[Sum[Mat[[i,j]],{i,k,l-1},{j,i+1,l}]]],
			{k,1,m},{l,k+1,m}]]<=$QuiverPrecision,
		Print["CoulombF: Unstable starting point"]];
  ];
  Which[
	Length[Mat]>1,
		Product[UnitStepWarn[Mat[[i,i+1]]Sum[Cvec[[j]],{j,1,i}]]
			(-1)^(UnitStepWarn[-Mat[[i,i+1]]]),{i,m-1}]
		+If[$QuiverNoLoop,0, 
           Sum[
			If[Sum[Mat[[i,j]],{i,k,l-2},{j,i+2,l}]!=0,
			Module[{lambda=-Sum[Mat[[i,i+1]],{i,k,l-1}]/Sum[Mat[[i,j]],{i,k,l-2},{j,i+2,l}]},
			    Apply[CoulombF,MatRedC[Matlambda[Mat,lambda],Cvec,
                    Flatten[{Table[{i},{i,k-1}],{Table[i,{i,k,l}]},Table[{i},{i,l+1,m}]},1]]] 
				CoulombG[Take[Matlambda[Mat,lambda],{k,l},{k,l}]]
				UnitStepWarn[-Sum[Mat[[i,i+1]],{i,k,l-1}]Sum[Mat[[i,j]],{i,k,l-1},{j,i+1,l}]]
				(-1)^(1+UnitStepWarn[Sum[Mat[[i,j]],{i,k,l-2},{j,i+2,l}]])],0]
		     ,{k,1,m-1},{l,k+2,m}]
		 ],
	Length[Mat]==1,1
]],
$QuiverRecursion==1,
        Module[{m=Length[Mat]},
    If[$QuiverVerbose,
    If[Length[Cvec]!=m,Print["CoulombF: Length of DSZ matrix and FI vector do not match !"]];
       If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
        Print["CoulombF: DSZ matrix is not antisymmetric !"]];
     If[Abs[Plus@@Cvec]>$QuiverPrecision,
    Print["CoulombF: FI terms do not sum up to zero !"]];
    If[Min[Table[If[l-k+1<Length[Cvec],Abs[Sum[Cvec[[i]],{i,k,l}]],1],
            {k,1,m},{l,k,m}]]<=$QuiverPrecision,
    Print["CoulombF: FI sit on wall of marginal stability"]];
    If[Min[Table[Abs[Sum[Mat[[i,m]],{i,k,m-1}]],
            {k,1,m-1}]]<=$QuiverPrecision,
    Print["CoulombF: Unstable starting point"]]
    If[Min[Table[Min[Abs[Sum[Mat[[i,i+1]],{i,k,l-1}]],Abs[Sum[Mat[[i,j]],{i,k,l-1},{j,i+1,l}]]],
        {k,1,m},{l,k+1,m}]]<=$QuiverPrecision,
  Print["CoulombF: Unstable starting point"]];
                                       ];
    Which[
    Length[Mat]>1,
    UnitStepWarn[-Mat[[m-1,m]] Cvec[[m]]]
    (-1)^(UnitStepWarn[-Mat[[m-1,m]]])
    CoulombF[Take[Mat, {1, m-1}, {1, m-1}], Flatten[{Take[Cvec, {1,m-2}],
            Cvec[[m-1]]+ Cvec[[m]]}]]
        +If[$QuiverNoLoop,0,
        Sum[CoulombF[MNewF[Mat,k], CNewF[Cvec,k]] CoulombG[MNewG[Mat,k]]
        UnitStepWarn[-Sum[Sum[Mat[[i,j]],{j, i+1,m}], {i,k+1,m-1}]     
        Sum[Sum[Mat[[i,j]],{j, i+1,m-1}], {i,k+1,m-2}] ]
    (-1)^(UnitStepWarn[- Sum[Mat[[i,m]], {i,k+1,m-1}]]), {k, 0, m-3}]
 ],
        Length[Mat]==1,1
]]];

(* induction rule for G *)
CoulombG[Mat_]:=Module[{m=Length[Mat]},
  If[$QuiverVerbose,
    If[$QuiverNoLoop,Print["CoulombG: should not be called since no loop assumed !"]];
    If[m<2, Print["CoulombG: requires at least 2 centers !"]];
    If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["CoulombG: DSZ matrix is not antisymmetric !"]];
    If[(m>2) && (Min[Table[Abs[Mat[[i,j]]],{i,m},{j,i+1,m}]]<=$QuiverPrecision),
		Print["CoulombG: Beware, some alpha(i,j) vanishes !"]];
    If[Abs[Sum[Mat[[i,j]],{i,m},{j,i+1,m}]]>$QuiverPrecision,
		Print["CoulombG: Total angular momentum does not vanish !"]];
  ];
  Which[m>3, Plus@@{
(* value at mu=0 *)
	(-1)^(1+UnitStepWarn[Mat[[m-1,m]]]) UnitStepWarn[-Mat[[m-1,m]] Sum[Mat[[i,m]],{i,m-1}]]
	CoulombG[Take[Matmu[Mat,0],{1,m-1},{1,m-1}]],
(* type 1 contribution: (m-2,m-1,m) form scaling subset *)
	Module[{mu1=-Mat[[m-2,m-1]]/(Mat[[m-2,m]]+Mat[[m-1,m]])},
	CoulombG[MatRed[Matmu[Mat,mu1],Flatten[{Table[{i},{i,m-3}],{Table[i,{i,m-2,m}]}},1]]] 
    CoulombG[Take[Matmu[Mat,mu1],{m-2,m},{m-2,m}]]
    (-1)^(1+UnitStepWarn[Mat[[m-2,m]]+Mat[[m-1,m]]]) 
    UnitStepWarn[-(Mat[[m-2,m-1]]+Mat[[m-1,m]]+Mat[[m-2,m]])Mat[[m-2,m-1]]]],
(* type 2 contribution, k=2: (2,...m-3) form scaling subset *)
	If[m>4, 
      Module[{mu2=(Sum[Mat[[i,j]],{i,2,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Mat[[1,m]]},
      UnitStepWarn[-Sum[Mat[[i,j]],{i,2,m-1},{j,i+1,m}]
        (Sum[Mat[[i,j]],{i,2,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])]
      (-1)^(1+UnitStepWarn[-Mat[[1,m]]])
      CoulombG[Take[Matmu[Mat,mu2],{2,m},{2,m}]]]
    ,0],
(* type 2 contributions, k>2 *)
	Sum[Module[{mu2=(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Sum[Mat[[i,m]],{i,k-1}]},
      CoulombG[MatRed[Matmu[Mat,mu2],Flatten[{Table[{i},{i,k-1}],{Table[i,{i,k,m}]}},1]]] 
      CoulombG[Take[Matmu[Mat,mu2],{k,m},{k,m}]]
	  (-1)^(1+UnitStepWarn[-Sum[Mat[[i,m]],{i,k-1}]]) 
	  UnitStepWarn[-(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m}])
		(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])]],{k,3,m-3}],
(* type 3 contributions *)
	Sum[Module[{mu3=(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Sum[Mat[[i,m]],{i,m-1}]},
      CoulombG[MatRed[Matmu[Mat,mu3],Flatten[{Table[{i},{i,k-1}],{Table[i,{i,k,m-1}]},{{m}}},1]]]
      CoulombG[Take[Matmu[Mat,mu3],{k,m-1},{k,m-1}]]
      (-1)^(1+UnitStepWarn[-Sum[Mat[[i,m]],{i,m-1}]]) 
      UnitStepWarn[-(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}])
     (Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])]],{k,2,m-3}]
},
(* initialize recursion for 3 or less centers *)
m==3,UnitStepWarn[Mat[[1,2]]Mat[[2,3]]](-1)^(1+UnitStepWarn[Mat[[1,2]]]),
m==2,1 (* this allows to get type 1, m=4 or type 2, k=2 contributions *) ,
m==1,1 (* this case should never arise *)
]];

(* optimized routines *)
MatRedOpt[Mat_,k_]:=Module[{m=Length[Mat],Matdef=Take[Mat,{1,k},{1,k}],i=1},
Do[Matdef[[i,k]]=Sum[Mat[[i,j]],{j,k,m}];
    Matdef[[k,i]]=- Matdef[[i,k]];,{i,k-1}];
Matdef];

MatRedOpt2[Mat_,k_]:=Module[{m=Length[Mat],Matdef=Take[Mat,{1,k+1},{1,k+1}],i=1},
Do[Matdef[[i,k]]=Sum[Mat[[i,j]],{j,k,m-1}];
    Matdef[[i,k+1]]=Mat[[i,m]];
    Matdef[[k,i]]=- Matdef[[i,k]];
    Matdef[[k+1,i]]=- Matdef[[i,k+1]];,{i,k-1}];
      Matdef[[k,k+1]]=Sum[Mat[[i,m]],{i,k,m-1}];
      Matdef[[k+1,k]]=-Matdef[[k,k+1]];
Matdef];

MatmuOpt[Mat_,mu_]:=Module[{m,Matdef},
m=Length[Mat];
If[m<=1,Print["MatmuOpt: rank <=1"]];
Matdef=Mat;
Do[Matdef[[i,m]]=mu Matdef[[i,m]];Matdef[[m,i]]=mu Matdef[[m,i]];,{i,m}];
Matdef[[m-3,m-1]]=Mat[[m-3,m-1]]+(1-mu) Sum[Mat[[k,Length[Mat]]],{k,Length[Mat]-1}];
Matdef[[m-1,m-3]]=-Matdef[[m-3,m-1]];
Matdef];

MNewFOpt[Mat_, k_] :=Module[{la},
If[Length[Mat]<=1,Print["MNewFOpt: rank <=1"]];
If[Length[k]>0,Print["MNewFOpt: rank k > 0"]];
la=(-Sum[
                       Sum[Mat[[s, j]], {j, s + 1, Length[Mat]-1}], {s, k + 1,
                           Length[Mat] - 2}]/
                 Sum[Mat[[s, Length[Mat]]], {s, k + 1, Length[Mat] -1}]);
    Flatten[{Table[Flatten[{Take[Mat, {i, i}, {1, k}],
    Sum[Mat[[i, j]], {j, k + 1, Length[Mat] - 1}]+
    Mat[[i, Length[Mat]]] la }], {i, 1, k}],
    {Flatten[{Table[-Sum[Mat[[i, j]], {j, k + 1, Length[Mat] - 1}]
                      - Mat[[i, Length[Mat]]] la, {i,1,k}], 0}]}}, 1]];

MNewGOpt[Mat_, k_] :=Module[{la},
If[Length[Mat]<=1,Print["MNewGOpt: rank <=1"]];
If[Length[k]>0,Print["MNewGOpt: rank k > 0"]];
la=(-Sum[
                       Sum[Mat[[s, j]], {j, s + 1, Length[Mat]-1}], {s, k + 1,
                           Length[Mat] - 2}]/
                 Sum[Mat[[s, Length[Mat]]], {s, k + 1,
    Length[Mat] -1}]);
    Flatten[{Table[Flatten[{Take[Mat, {i, i}, {k+1, Length[Mat]-1}],
    la  Mat[[i, Length[Mat]]]}], {i, k+1, Length[Mat]-1}],
   {Flatten[{Table[-(la Mat[[i, Length[Mat]]]), {i,k+1, Length[Mat]-1}], 0}]}}, 1]];

CoulombIndexOpt[Mat_,PMat_,Cvec_,y_]:=Module[{m,ListPerm,i,j,k,RMat,RCvec},
	m=Length[Cvec];
	If[$QuiverVerbose,
		If[Max[Flatten[PMat-Mat]]>1/2,Print["CoulombIndexOpt: PMat is not close to Mat !"]];
        If[Abs[Plus@@Cvec]>$QuiverPrecision,Print["CoulombIndexOpt: CVec does not sum to zero !"]];
	];
	ListPerm=Permutations[Range[m]];
    Do[ If[Abs[Sum[Cvec[[ListPerm[[j,i]]]],{i,k}]]<=$QuiverPrecision, 
           If[Abs[Sum[Mat[[ListPerm[[j,i1]],ListPerm[[j,i2]]]],
                {i1,k},{i2,k+1,m}]]>$QuiverPrecision,
               Print["CoulombIndex: FI sit on wall of marginal stability"];Break[]];
          ],{k,1,IntegerPart[m/2]},{j,Length[ListPerm]}
    ];
	(* RMat is a further eps_ 2 perturbation *)
	RMat=Table[Random[Integer,{1,100000}],{i,m},{j,m}];	
	RMat=1/100000/$QuiverPerturb2 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,m},{j,m}];
	RCvec=1/1000/$QuiverPerturb2 Table[Random[Integer,{1,1000}],{i,m}];
	RCvec[[m]]=-Sum[RCvec[[i]],{i,m-1}];
	If[$QuiverVerbose && m>3,PrintTemporary["CoulombIndexOpt: evaluating for ",m," centers"]];
	(y-1/y)^(1-m) (-1)^(Sum[QuiverMultiplierMat[i,j] Mat[[i,j]],{i,Length[Cvec]},{j,i+1,m}]+m-1)	   
	Sum[y^(Sum[QuiverMultiplierMat[ListPerm[[k,i]],ListPerm[[k,j]]] Mat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,i+1,m}])
		CoulombFOpt[Table[PMat[[ListPerm[[k,i]],ListPerm[[k,j]]]]+
					   RMat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,m}],
                 Table[Cvec[[ListPerm[[k,i]]]]+RCvec[[ListPerm[[k,i]]]],{i,m}]],
       {k,Length[ListPerm]}]
];

(* induction rule for F, improved *)
CoulombFOpt[Mat_,Cvec_]:=
        Module[{m=Length[Mat]},
  If[m>1,
    If[Mat[[m-1,m]] Cvec[[m]]<0,  If[Mat[[m-1,m]]>0,1,-1]
    CoulombFOpt[Take[Mat, {1, m-1}, {1, m-1}], Flatten[{Take[Cvec, {1,m-2}],
            Cvec[[m-1]]+ Cvec[[m]]}]],0]
        +If[$QuiverNoLoop,0,
        Sum[
        If[-Sum[Sum[Mat[[i,j]],{j, i+1,m}], {i,k+1,m-1}] 
            Sum[Sum[Mat[[i,j]],{j, i+1,m-1}], {i,k+1,m-2}] >0,
          If[Sum[Mat[[i,m]], {i,k+1,m-1}]>0,
          CoulombFOpt[MNewFOpt[Mat,k], CNewF[Cvec,k]] CoulombGOpt[MNewGOpt[Mat,k]],
          -CoulombFOpt[MNewFOpt[Mat,k], CNewF[Cvec,k]] CoulombGOpt[MNewGOpt[Mat,k]]
          ],
        If[-Sum[Sum[Mat[[i,j]],{j, i+1,m}], {i,k+1,m-1}] 
            Sum[Sum[Mat[[i,j]],{j, i+1,m-1}], {i,k+1,m-2}]==0,
          If[$QuiverVerbose, Message[UnitStepWarn::zero]]
          If[Sum[Mat[[i,m]], {i,k+1,m-1}]>0,
          1/2 CoulombFOpt[MNewFOpt[Mat,k], CNewF[Cvec,k]] CoulombGOpt[MNewGOpt[Mat,k]],
          -1/2 CoulombFOpt[MNewFOpt[Mat,k], CNewF[Cvec,k]] CoulombGOpt[MNewGOpt[Mat,k]]
          ]
        ,0]], 
        {k, 0, m-3}]],
 If[m==1,1,0]
]];

(* induction rule for G *)
CoulombGOpt[Mat_]:=Module[{m=Length[Mat],g=0.,mu1,mu2,i=1,j=1,k=1},
If[m==3,If[Mat[[1,2]]Mat[[2,3]]>0,If[Mat[[1,2]]>0,g=1,g=-1],g=0],If[m==2,g=1,
If[m==1, g=1,
If[ m>3,
mu1=-Mat[[m-2,m-1]]/(Mat[[m-2,m]]+Mat[[m-1,m]]);
mu2=(Sum[Mat[[i,j]],{i,2,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Mat[[1,m]];
g=(* value at mu=0 *)Plus@@{
   If[Mat[[m-1,m]]Sum[Mat[[i,m]],{i,m-1}]<0,
     If[Mat[[m-1,m]]>0,
       CoulombGOpt[Take[MatmuOpt[Mat,0],{1,m-1},{1,m-1}]],
      -CoulombGOpt[Take[MatmuOpt[Mat,0],{1,m-1},{1,m-1}]]],   
   If[Mat[[m-1,m]]Sum[Mat[[i,m]],{i,m-1}]<0,
     If[$QuiverVerbose, Message[UnitStepWarn::zero]]
     If[Mat[[m-1,m]]==0,
       1/2 CoulombGOpt[Take[MatmuOpt[Mat,0],{1,m-1},{1,m-1}]],
      -1/2 CoulombGOpt[Take[MatmuOpt[Mat,0],{1,m-1},{1,m-1}]]],
   0]]
,(* type 1 contribution: (m-2,m-1,m) form scaling subset *)
 If[(Mat[[m-2,m-1]]+Mat[[m-1,m]]+Mat[[m-2,m]])Mat[[m-2,m-1]]<0,
   If[Mat[[m-2,m]]+Mat[[m-1,m]]>0,
    CoulombGOpt[MatRedOpt[MatmuOpt[Mat,mu1],m-2]] CoulombGOpt[Take[MatmuOpt[Mat,mu1],{m-2,m},{m-2,m}]],
   -CoulombGOpt[MatRedOpt[MatmuOpt[Mat,mu1],m-2]] CoulombGOpt[Take[MatmuOpt[Mat,mu1],{m-2,m},{m-2,m}]]]
   ,
  If[(Mat[[m-2,m-1]]+Mat[[m-1,m]]+Mat[[m-2,m]])Mat[[m-2,m-1]]==0,
   If[$QuiverVerbose, Message[UnitStepWarn::zero]]
   If[Mat[[m-2,m]]+Mat[[m-1,m]]>0,
    1/2 CoulombGOpt[MatRedOpt[MatmuOpt[Mat,mu1],m-2]] CoulombGOpt[Take[MatmuOpt[Mat,mu1],{m-2,m},{m-2,m}]],
   -1/2 CoulombGOpt[MatRedOpt[MatmuOpt[Mat,mu1],m-2]] CoulombGOpt[Take[MatmuOpt[Mat,mu1],{m-2,m},{m-2,m}]]]
   ,
  0]],
(* type 2 contribution, k=2: (2,...m-3) form scaling subset *)
If[m>4, 
     If[Sum[Mat[[i,j]],{i,2,m-1},{j,i+1,m}]
        (Sum[Mat[[i,j]],{i,2,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])<0,If[Mat[[1,m]]>0,-CoulombGOpt[Take[MatmuOpt[Mat,mu2],{2,m},{2,m}]],CoulombGOpt[Take[MatmuOpt[Mat,mu2],{2,m},{2,m}]]],0] 
    ,0],(* type 2 contributions, k>2 *)	Sum[Module[{mu3=(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Sum[Mat[[i,m]],{i,k-1}]},
	If[(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m}])
		(Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])<0,
     If[Sum[Mat[[i,m]],{i,k-1}]>0,
      -CoulombGOpt[MatRedOpt[MatmuOpt[Mat,mu3],k]] CoulombGOpt[Take[MatmuOpt[Mat,mu3],{k,m},{k,m}]] , 
      CoulombGOpt[MatRedOpt[MatmuOpt[Mat,mu3],k]] CoulombGOpt[Take[MatmuOpt[Mat,mu3],{k,m},{k,m}]] ]
    ,
	If[(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m}])
		(Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])==0,
     If[$QuiverVerbose, Message[UnitStepWarn::zero]]
     If[Sum[Mat[[i,m]],{i,k-1}]>0,
      -1/2 CoulombGOpt[MatRedOpt[MatmuOpt[Mat,mu3],k]] CoulombGOpt[Take[MatmuOpt[Mat,mu3],{k,m},{k,m}]] , 
      1/2 CoulombGOpt[MatRedOpt[MatmuOpt[Mat,mu3],k]] CoulombGOpt[Take[MatmuOpt[Mat,mu3],{k,m},{k,m}]] ]
    ,0]]],{k,3,m-3}],
(* type 3 contributions *)	
 Sum[Module[{mu4=(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Sum[Mat[[i,m]],{i,m-1}]},
    If[(Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}])
     (Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])<0,
    If[Sum[Mat[[i,m]],{i,m-1}]>0,
      -CoulombGOpt[MatRedOpt2[MatmuOpt[Mat,mu4],k]]CoulombGOpt[Take[MatmuOpt[Mat,mu4],{k,m-1},{k,m-1}]], 
      CoulombGOpt[MatRedOpt2[MatmuOpt[Mat,mu4],k]] CoulombGOpt[Take[MatmuOpt[Mat,mu4],{k,m-1},{k,m-1}]]]
    ,
    If[(Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}])
     (Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])==0,
     If[$QuiverVerbose, Message[UnitStepWarn::zero]]
    If[Sum[Mat[[i,m]],{i,m-1}]>0,
      -1/2 CoulombGOpt[MatRedOpt2[MatmuOpt[Mat,mu4],k]]CoulombGOpt[Take[MatmuOpt[Mat,mu4],{k,m-1},{k,m-1}]], 
      1/2 CoulombGOpt[MatRedOpt2[MatmuOpt[Mat,mu4],k]] CoulombGOpt[Take[MatmuOpt[Mat,mu4],{k,m-1},{k,m-1}]]]
    ,0]]],{k,2,m-3}]},g=0;]]];g]];
    
    CoulombTestOrdering[Mat_,Cvec_,Li_]:=Module[{m,CoulombHessian,Eq,soN,
    Listimsol,Listrealsol,Listord,Listcorrectord,z},
	m=Length[Cvec];
    If[$QuiverVerbose,
      If[m>5,Print["CoulombFNum: the number of centers may be too high for NSolve !"]];  
      If[Length[Cvec]!=m,Print["CoulombFNum: Length of DSZ matrix and FI vector do not match !"]];
      If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["CoulombFNum: DSZ matrix is not antisymmetric !"]];
      If[Abs[Plus@@Cvec]>$QuiverPrecision,
		Print["CoulombFNum: FI terms do not sum up to zero !"]];
      If[Min[Table[If[l-k+1<Length[Cvec],Abs[Sum[Cvec[[i]],{i,k,l}]],1],
			{k,1,m},{l,k,m}]]<=$QuiverPrecision,
		Print["CoulombFNum: FI sit on wall of marginal stability"]];
      If[Min[Table[Abs[Mat[[i,i+1]]],{i,m-1}]]<=$QuiverPrecision,
		Print["CoulombFNum: Some alpha(i,i+1) vanishes !"]];
      If[Min[Table[Min[Abs[Sum[Mat[[i,i+1]],{i,k,l-1}]],Abs[Sum[Mat[[i,j]],{i,k,l-1},{j,i+1,l}]]],
			{k,1,m},{l,k+1,m}]]<=$QuiverPrecision,
		Print["CoulombFNum: Unstable starting point, try another perturbation"]];
    ];
	CoulombHessian=Table[If[i==j,Mat[[1,i]] z[i]/Abs[z[i]]^3
     +Sum[If[i==k,0,Mat[[i,k]](z[k]-z[i])/Abs[z[k]-z[i]]^3],{k,2,m}],
     -Mat[[i,j]](z[j]-z[i])/Abs[z[j]-z[i]]^3],{i,2,m},{j,2,m}];
	Eq=Flatten[{Table[Sum[If[i==j,0,Mat[[Li[[i]],Li[[j]]]]/(z[Li[[j]]]-z[Li[[i]]])
		Sign[j-i]],{j,m}]-Cvec[[Li[[i]]]],{i,m-1}],{z[1]}}];
	soN=NSolve[Eq==0];
	Listimsol=Table[Chop[Im[Table[z[i],{i,m}]/.soN[[j]]]],{j,Length[soN]}];
	Listrealsol=Flatten[Position[Listimsol,Table[0,{i,m}]]];
	Listord=Table[Table[z[Li[[i]]]<=z[Li[[i+1]]],{i,m-1}]/.{z[i_]->Re[z[i]]}/.soN[[Listrealsol[[j]]]],{j,Length[Listrealsol]}];
	Listcorrectord=Flatten[Position[Listord,Table[True,{i,m-1}]]];
	If[Length[Listcorrectord]>0,
	  Table[ Sign[Det[(CoulombHessian/.{z[i_]->Re[z[i]]
       } /.soN[[Listrealsol[[Listcorrectord[[j]]]]]])]],{j,Length[Listcorrectord]}],
      {}]
    ];

CoulombFNum[Mat_,Cvec_]:=CoulombTestOrdering[Mat,Cvec,Range[Length[Mat]]];

CoulombGNum[Mat_]:=Module[{m,W,vars,Eq,d2W,soN,Listimsol,Listrealsol,Listord,
                           Listcorrectord,z},
    m=Length[Mat];
    If[$QuiverVerbose,
      If[$QuiverNoLoop,Print["CoulombGNum: should not be called since no loop assumed !"]];
      If[m<2, Print["CoulombGNum: requires at least 2 centers !"]];
      If[m>6,Print["CoulombGNum: the number of centers may be too high for NSolve !"]]; 
      If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["CoulombGNum: DSZ matrix is not antisymmetric !"]];
      If[(m>2) && (Min[Table[Abs[Mat[[i,j]]],{i,m},{j,i+1,m}]]<=$QuiverPrecision),
		Print["CoulombGNum: Beware, some alpha(i,j) vanishes !"]];
      If[Abs[Sum[Mat[[i,j]],{i,m},{j,i+1,m}]]>$QuiverPrecision,
		Print["CoulombGNum: Total angular momentum does not vanish !"]];
    ];
	W=-Sum[Mat[[i,j]]Log[z[j]-z[i]],{i,m-1},{j,i+1,m}]/.{z[1]->0,z[m]->1};
	vars=Table[z[i],{i,2,m-1}];
	Eq=Table[D[W,vars[[i]]],{i,m-2}];
	d2W=Det[Table[D[D[W,vars[[i]]],vars[[j]]],{i,Length[vars]},{j,Length[vars]}]];
	soN=NSolve[Eq==0,vars];
	Listimsol=Table[Chop[Im[Table[z[i],{i,2,m-1}]/.soN[[j]]]],{j,Length[soN]}];
	Listrealsol=Flatten[Position[Listimsol,Table[0,{i,m-2}]]];
	Listord=Table[Table[z[i+1]>z[i],{i,m-1}]/.{z[1]->0,z[m]->1}/.{z[i_]->Re[z[i]]}/.soN[[Listrealsol[[j]]]],{j,Length[Listrealsol]}];
	Listcorrectord=Flatten[Position[Listord,Table[True,{i,m-1}]]];
	If[Length[Listcorrectord]>0,
	Sign[d2W/.{z[i_]->Re[z[i]]}/.soN[[Listrealsol[[Listcorrectord[[1]]]]]]],0]
];

CoulombIndexNum[Mat_,PMat_,Cvec_,y_]:=Module[{m,ListPerm,CoulombHessian,
	  CoulombOrderings,Eq,soN,RMat,RCvec,Listimsol,Listrealsol,Listord,Listcorrectord,z},
	m=Length[Cvec];
	If[Abs[Plus@@Cvec]>$QuiverPrecision,
		Print["CoulombIndexNum: c_i do not sum up to zero"]];
    If[Max[Flatten[PMat-Mat]]>1/2,Print["CoulombIndexNum: PMat is not close to Mat !"]];
	RMat=Table[Random[Integer,{1,1000}],{i,m},{j,m}];
	RMat=1/1000/$QuiverPerturb2 Table[Which[
		i<j,RMat[[i,j]],
		i>j,-RMat[[j,i]],
		i==j,0],{i,m},{j,m}];
	RCvec=1/1000/$QuiverPerturb2 Table[Random[Integer,{1,1000}],{i,m}];
	RCvec[[m]]=-Sum[RCvec[[i]],{i,m-1}];
	ListPerm=DeleteDuplicates[Permutations[Range[m]],#1==Reverse[#2]&];
    Do[ If[Abs[Sum[Cvec[[ListPerm[[j,i]]]],{i,k}]]<=$QuiverPrecision, 
           If[Abs[Sum[Mat[[ListPerm[[j,i1]],ListPerm[[j,i2]]]],
                {i1,k},{i2,k+1,m}]]>$QuiverPrecision,
               Print["CoulombIndexNum: FI sit on wall of marginal stability"];Break[]];
          ],{k,1,IntegerPart[m/2]},{j,Length[ListPerm]}
    ];	
CoulombOrderings=Select[Table[
	  CoulombHessian=Table[If[i==j,(PMat[[1,i]]+RMat[[1,i]]) z[i]/Abs[z[i]]^3+Sum[If[i==k,0,(PMat[[i,k]]+RMat[[i,k]])(z[k]-z[i])/Abs[z[k]-z[i]]^3],{k,2,Length[Cvec]}],-(PMat[[i,j]]+RMat[[i,j]])(z[j]-z[i])/Abs[z[j]-z[i]]^3],{i,2,m},{j,2,m}];
	  Eq=Flatten[{Table[Sum[If[i==j,0,
        (PMat[[ListPerm[[pa,i]],ListPerm[[pa,j]]]]+RMat[[ListPerm[[pa,i]],ListPerm[[pa,j]]]])
        /(z[ListPerm[[pa,j]]]-z[ListPerm[[pa,i]]])Sign[j-i]],{j,Length[Cvec]}]
        -Cvec[[ListPerm[[pa,i]]]]-RCvec[[ListPerm[[pa,i]]]],{i,m}]==0,z[1]==0}];
PrintTemporary["Solving with ordering ",pa];
	  soN=NSolve[Eq,Table[z[i],{i,m}]];
	  Listimsol=Table[Chop[Im[Table[z[i],{i,m}]/.soN[[j]]]],{j,Length[soN]}];
	  Listrealsol=Flatten[Position[Listimsol,Table[0,{i,m}]]];
Listord=Table[Table[z[ListPerm[[pa,i]]]<=z[ListPerm[[pa,i+1]]],{i,m-1}]/.{z[i_]->Re[z[i]]}/.soN[[Listrealsol[[j]]]],{j,Length[Listrealsol]}];
	  Listcorrectord=Flatten[Position[Listord,Table[True,{i,m-1}]]];
	  If[Length[Listcorrectord]>1,Print["CoulombIndexNum: ",ListPerm[[pa]]," gives ",Length[Listcorrectord]," solutions"]];
	  If[Length[Listcorrectord]>0,
Print[ {ListPerm[[pa]],
		Sum[Mat[[ListPerm[[pa,i]],ListPerm[[pa,j]]]],{i,m},{j,i+1,m}],
		Sum[Sign[Det[(CoulombHessian/.{z[i_]->Re[z[i]]}/.
			soN[[Listrealsol[[Listcorrectord[[j]]]]]])]],{j,Length[Listcorrectord]}]}];
	   {ListPerm[[pa]],
		Sum[Mat[[ListPerm[[pa,i]],ListPerm[[pa,j]]]],{i,m},{j,i+1,m}],
		Sum[Sign[Det[(CoulombHessian/.{z[i_]->Re[z[i]]}/.
			soN[[Listrealsol[[Listcorrectord[[j]]]]]])]],{j,Length[Listcorrectord]}]}]
		,{pa,1,Length[ListPerm]}]
,Length[#]>0&
    ];
    Print["CoulombIndexNum:",Table[CoulombOrderings[[i,1]],{i,Length[CoulombOrderings]}]];
	Simplify[(-1)^(Sum[$QuiverMultiplier Mat[[i,j]],{i,m},{j,i+1,m}]+m-1)
Table[CoulombOrderings[[i,3]](y^($QuiverMultiplier CoulombOrderings[[i,2]])+(-1)^(m+1)
y^(-$QuiverMultiplier CoulombOrderings[[i,2]])),{
	i,Length[CoulombOrderings]}]/(y-1/y)^(m-1)]];

(* evaluate Coulombg numerically *)
EvalCoulombIndexNum[Mat_,PMat_,Cvec_,f_]:=f/.{Coulombg[Li_,y_]:>CoulombIndexNum[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]};



(* ::Section:: *)
(*Coulomb branch formula *)


CoulombBranchFormula[Mat_,Cvec_,Nvec_]:=Module[{RMat,QPoinca,ListH,ListCoef,soMinimalModif,soH,Cvec0},
  If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
      Print["CoulombBranchFormula: Length of DSZ matrices, FI and dimension vectors do not match !"]];
  If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["CoulombBranchFormula: DSZ matrix is not antisymmetric !"]];
  If[Max[Nvec]<0,Print["CoulombBranchFormula: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
  Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,       
		Print["CoulombBranchFormula: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0];
  ];  
  RMat=Table[Random[Integer,{1,1000}],{i,Length[Mat]},{j,Length[Mat]}];
  RMat=1/1000/$QuiverPerturb1 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,Length[Mat]},{j,Length[Mat]}];
  If[$QuiverVerbose,PrintTemporary["CoulombBranchFormula: Constructing Poincar\[EAcute] polynomial..."]]; 
  QPoinca=SimplifyOmSmultbasis[
	QuiverPoincarePolynomialExpand[Mat,Mat+RMat,Cvec0,Nvec,QuiverPoincarePolynomial[Nvec,y]]];
  If[$QuiverNoLoop,
    If[$QuiverDisplayCoulombH,
       {SwapFugacity[SimplifyOmSbasis[QPoinca/.{CoulombH[x__]:>0}]],{}},
       SwapFugacity[SimplifyOmSbasis[QPoinca/.{CoulombH[x__]:>0}]]
    ]   
  ,
  (*else *)  
     Module[{},
       soH=CoulombHSubQuivers[Mat,Mat+RMat,Nvec,y];
       {ListH,ListCoef}=ListCoulombH[Nvec,QPoinca];       
       If[Length[ListH]==0,
		soMinimalModif={},
        soMinimalModif=Simplify[SolveCoulombH[ListH,ListCoef,soH],
             $QuiverMultiplierAssumption]]
     ];
     If[$QuiverVerbose,PrintTemporary["CoulombBranchFormula: Substituting CoulombH factors..."]]; 
     If[$QuiverDisplayCoulombH,
       {SwapFugacity[SimplifyOmSbasis[QPoinca/.soMinimalModif/.soH]],
Union[Flatten[{soH,soMinimalModif}]]/.y$->y},
        SwapFugacity[SimplifyOmSbasis[QPoinca/.soMinimalModif/.soH]]
     ]
  ]
];

CoulombBranchFormula[Mat_,Cvec_,Nvec_,y_]:=Module[{},
  Print["CoulombBranchFormula: Obsolete syntax, argument y should be dropped"];
  CoulombBranchFormula[Mat,Cvec,Nvec]
];

CoulombBranchFormulaFromH[Mat_,Cvec_,Nvec_,soH_]:=Module[{RMat,QPoinca,Cvec0=Cvec},
  If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
      Print["CoulombBranchFormulaFromH: Length of DSZ matrices, FI and dimension vectors do not match !"]];
  If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["CoulombBranchFormulaFromH: DSZ matrix is not antisymmetric !"]];
  If[Max[Nvec]<0,Print["CoulombBranchFormulaFromH: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
  Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,      
		Print["CoulombBranchFormulaFromH: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0];
  ];
  RMat=Table[Random[Integer,{1,1000}],{i,Length[Mat]},{j,Length[Mat]}];
  RMat=1/1000/$QuiverPerturb1 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,Length[Mat]},{j,Length[Mat]}];
  PrintTemporary["CoulombBranchFormulaFromH: Constructing Poincar\[EAcute] polynomial..."]; 
  QPoinca=SimplifyOmSmultbasis[
	QuiverPoincarePolynomialExpand[Mat,Mat+RMat,Cvec0,Nvec,QuiverPoincarePolynomial[Nvec,y]]];
  If[$QuiverNoLoop,
       SwapFugacity[SimplifyOmSbasis[QPoinca/.{CoulombH[x__]:>0}]]       
  , (*else *)  
     Module[{},
       If[$QuiverVerbose,PrintTemporary["CoulombBranchFormulaFromH: Substituting your CoulombH factors..."]]; 
       SwapFugacity[SimplifyOmSbasis[QPoinca/.soH]]
     ]
  ]
];

CoulombBranchFormulaFromH[Mat_,Cvec_,Nvec_,soH_,y_]:=Module[{},
  Print["CoulombBranchFormulaFromH: Obsolete syntax, argument y should be dropped"];
  CoulombBranchFormulaFromH[Mat,Cvec,Nvec,soH]
];





(* step by step *)

QuiverPoincarePolynomialRat[gam_,y_]:=Module[{ListAllPart},
	ListAllPart=ListAllPartitions[gam];
    Sum[Coulombg[ListAllPart[[i]],y]SymmetryFactor[ListAllPart[[i]]]
		Product[OmTRat[ListAllPart[[i,j]],y],{j,Length[ListAllPart[[i]]]}],
		{i,Length[ListAllPart]}]];

QuiverPoincarePolynomial[gam_,y_]:=DivisorSum[GCD@@gam,
	MoebiusMu[#]/# (y-1/y)/(y^#-y^(-#)) QuiverPoincarePolynomialRat[gam/#,y^#]&];

(* evaluate Coulombg using induction rule *)
EvalCoulombIndex[Mat_,PMat_,Cvec_,f_]:=f/.{Coulombg[Li_,y_]:>
  If[$QuiverCoulombOpt==1,CoulombIndexOpt[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y],
CoulombIndex[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]]};

(* evaluate Coulombg using induction rule in attractor chamber *)
EvalCoulombIndexAtt[Mat_,PMat_,f_]:=f/.{Coulombg[Li_,y_]:>
  If[$QuiverCoulombOpt==1,CoulombIndexOpt[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],-Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]},{j,Length[Li]}],
      {i,Length[Li]}],y],
CoulombIndex[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],-Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]},{j,Length[Li]}],
      {i,Length[Li]}],y]]};
      
QuiverPoincarePolynomialExpand[Mat_,PMat_,Cvec_,Nvec_,QPoinca_]:=OmSNoLoopToZero[Mat,
    CoulombHNoLoopToZero[PMat,
	OmTToOmS[EvalCoulombIndex[Mat,PMat,Cvec,OmTNoLoopToZero[PMat,QPoinca]]]]];

ListCoulombH[Nvec_,QPoinca_]:=Module[{Li,ListMonomials,ListCoulombHFac,ListCoeffMonomials,ListPick,
	ListCoeffMonomialsReduced,ListCoulombHReduced},
  Li=ListAllPartitionsMult[Nvec];
  ListMonomials=Table[Product[OmS[Li[[j,i,1]],y^Li[[j,i,2]]],{i,Length[Li[[j]]]}],{j,Length[Li]}];
  ListCoulombHFac=Table[
           CoulombH[Table[Li[[j,i,1]],{i,Length[Li[[j]]]}],
                    Table[Li[[j,i,2]],{i,Length[Li[[j]]]}],y],{j,Length[Li]}]; 
  ListCoeffMonomials=Table[Coefficient[QPoinca,ListMonomials[[i]]],{i,Length[ListMonomials]}];
  ListPick=Table[!(D[ListCoeffMonomials[[i]],ListCoulombHFac[[i]]]===0),{i,Length[ListMonomials]}];  
  ListCoeffMonomialsReduced=Pick[ListCoeffMonomials,ListPick];
  ListCoulombHReduced=Pick[ListCoulombHFac,ListPick];
  {ListCoulombHReduced,ListCoeffMonomialsReduced}
];

SolveCoulombH[ListCoulombHReduced_,ListCoeffMonomialsReduced_,soH_]:=Module[{soCoulombH},
	soCoulombH=Simplify[Solve[
       (ListCoeffMonomialsReduced/.soH)==0,ListCoulombHReduced][[1]]];
	Table[(ListCoulombHReduced[[i]]/.y->y_)->
      Simplify[-MinimalModif[ListCoulombHReduced[[i]]/.soCoulombH]
       +(ListCoulombHReduced[[i]]/.soCoulombH)]/.y->y$,{i,Length[ListCoulombHReduced]}]
];

CoulombHSubQuivers[Mat_,PMat_,Nvec_,y_]:=Module[{Li},
	Li=ListSubQuivers[Nvec];
	CoulombHSubQuiversFixedLevel[Mat,PMat,Li,(Plus@@Nvec)-1,y]
];

CoulombHSubQuiversFixedLevel[Mat_,PMat_,Li_,m_,y_]:=Module[{LiLevel,ListCoulombHLevel,QPoinca,ListH,ListCoef,
	soH,soMinimalModif},
	If[m<3,{},
	  LiLevel=Select[Li,Plus@@#==m&];	
		ListCoulombHLevel=CoulombHSubQuiversFixedLevel[Mat,PMat,Li,m-1,y];
		soH=ListCoulombHLevel;
		Do[
         If[$QuiverVerbose,PrintTemporary["Evaluating CoulombH factors for dimension vector ",LiLevel[[i]]]];
        QPoinca=SimplifyOmSmultbasis[QuiverPoincarePolynomialExpand[Mat,PMat,
                AttractorFI[Mat,LiLevel[[i]]]+
                RandomFI[LiLevel[[i]]]/$QuiverPerturb1,LiLevel[[i]],QuiverPoincarePolynomial[LiLevel[[i]],y]]];
	     {ListH,ListCoef}=ListCoulombH[LiLevel[[i]],QPoinca];
         If[Length[ListH]==0,
	      soMinimalModif={},    
          soMinimalModif=Simplify[SolveCoulombH[ListH,ListCoef,ListCoulombHLevel],
          $QuiverMultiplierAssumption\[Element]Integers];
		 soH=Append[soH,(soMinimalModif)];
		 ];
        ,{i,Length[LiLevel]}];	   
	Union[Flatten[soH]]
	]
];

(* minimal modif hypothesis , assuming that argument is invariant under y->1/y *)
MinimalModif[f_]:=Module[{A,ListZeros,u,so},
  If[IntegerQ[$QuiverMultiplier],
	A=(1/u-u)(f/.{y->u})/(1-u y)/(1-u/y);
	Residue[A,{u,0}],
 (* else *)
    so=Solve[Denominator[Factor[f]]==0,y,Complexes];
    If[Length[so]==0,ListZeros={},
	      ListZeros=Union[y/.Solve[Denominator[Factor[f]]==0,y,Complexes]]
    ];
	A=(1/u-u)(f/.{y->u})/(1-u y)/(1-u/y);
	(*-1/2Simplify[Residue[A,{u,y}]+Residue[A,{u,1/y}]*) 
	f-1/2Simplify[Sum[If[ListZeros[[i]]==0,0,Residue[A,{u,ListZeros[[i]]}]],{i,Length[ListZeros]}]]
 ]
];

MinimalModifFast[f_]:=Module[{u},Residue[(1/u-u)(f/.{y->u})/(1-u y)/(1-u/y),{u,0}]];


(* ::Section:: *)
(*Higgs branch formula *)


HiggsBranchFormula[Mat_,Cvec_,Nvec_]:=Module[{Cvec0},
  If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
      Print["HiggsBranchFormula: Length of DSZ matrices, FI and dimension vectors do not match !"]];
  If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["HiggsBranchFormula: DSZ matrix is not antisymmetric !"]];
  If[Max[Nvec]<0,Print["HiggsBranchFormula: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
  Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,
		Print["HiggsBranchFormula: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0];
  ];   
 EvalQFact[EvalHiggsG[Mat,Cvec0,OmbToHiggsG[OmToOmb[Om[Nvec,y]]]]]
];

HiggsBranchFormula[Mat_,Cvec_,Nvec_,y_]:=Module[{},
  Print["HiggsBranchFormula: Obsolete syntax, argument y should be dropped"];
  HiggsBranchFormula[Mat,Cvec,Nvec]
];

StackInvariant[Mat_,Cvec_,Nvec_,y_]:=Module[{m,JKListAllPermutations,pa,Cvec0},
  m=Length[Nvec];
  If[Max[Nvec]<0,Print["StackInvariant: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
  Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  pa=Flatten[Map[Permutations,ListAllPartitions[Nvec]],1];
  If[$QuiverVerbose,
    If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
        Print["StackInvariant: Length of DSZ matrix, FI and dimension vectors do not match !"]];
    If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["StackInvariant: DSZ matrix is not antisymmetric !"]];
  If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,
		Print["StackInvariant: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0];
    ];   
  PrintTemporary["StackInvariant: summing ", Length[pa]," ordered partitions"];
  ];
  (-y)^( Sum[-QuiverMultiplierMat[k,l] Max[Mat[[k,l]],0]Nvec[[k]]Nvec[[l]],{k,m},{l,m}]-1+Plus@@ Nvec)
	   (y^2-1)^(1-Plus@@Nvec)
	Sum[If[(Length[pa[[i]]]==1) ||And@@Table[Sum[Cvec0[[k]] pa[[i,a,k]],{a,b},{k,m}]>0,{b,Length[pa[[i]]]-1}],
      (-1)^(Length[pa[[i]]]-1)
       y^(2 Sum[Max[QuiverMultiplierMat[l,k] Mat[[l,k]],0] pa[[i,a,k]]pa[[i,b,l]],
    {a,1,Length[pa[[i]]]},{b,a,Length[pa[[i]]]},{k,m},{l,m}])/
    Product[QFact[pa[[i,j,k]],y] ,{j,1,Length[pa[[i]]]},{k,m}],0],{i,Length[pa]}]
];



AbelianStackInvariant[Mat_,Cvec_,y_]:=StackInvariant[Mat,Cvec,ConstantArray[1,Length[Cvec]],y];

(* AbelianStackInvariant[Mat_,Cvec_,y_]:=Module[{m,JKListAllPermutations,pa,ListPerm,Cvec0},
  m=Length[Cvec];
  If[Max[Nvec]<0,Print["AbelianStackInvariant: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
  If[$QuiverVerbose,
    If[Length[Union[{Length[Cvec],Length[Mat]}]]>1, 
        Print["AbelianStackInvariant: Length of DSZ matrix and FI  vectors do not match !"]];
    If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["AbelianStackInvariant: DSZ matrix is not antisymmetric !"]];
  Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  pa=Flatten[Map[Permutations,ListAllPartitions[ConstantArray[1,m]]],1];
  If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,
 		Print["AbelianStackInvariant: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0];
   ];   
   ListPerm=Permutations[Range[m]];
    Do[ If[Abs[Sum[Cvec0[[ListPerm[[j,i]]]],{i,k}]]<=$QuiverPrecision, 
           If[Abs[Sum[Mat[[ListPerm[[j,i1]],ListPerm[[j,i2]]]],
                {i1,k},{i2,k+1,m}]]>$QuiverPrecision,
               Print["AbelianStackInvariant: FI sit on wall of marginal stability"];
               Break[],
			   Print["AbelianStackInvariant: FI sit on wall of threshold stability"];
               Break[]
             ];
          ],{k,1,IntegerPart[m/2]},{j,Length[ListPerm]}
    ];
    PrintTemporary["AbelianStackInvariant: summing ", Length[pa]," ordered partitions"];
  ];	
  (-y)^($QuiverMultiplier Sum[-Max[Mat[[k,l]],0],{k,m},{l,m}]-1+m)
	   (y^2-1)^(1-m)
	Sum[If[(Length[pa[[i]]]==1) ||And@@Table[Sum[Cvec0[[k]] pa[[i,a,k]],{a,b},{k,m}]>0,
          {b,Length[pa[[i]]]-1}],
      (-1)^(Length[pa[[i]]]-1)
       y^(2$QuiverMultiplier  Sum[Max[Mat[[l,k]],0] pa[[i,a,k]]pa[[i,b,l]],
    {a,1,Length[pa[[i]]]},{b,a,Length[pa[[i]]]},{k,m},{l,m}])/
    Product[QFact[pa[[i,j,k]],y] ,{j,1,Length[pa[[i]]]},{k,m}],0],{i,Length[pa]}]
];
*)

QDeformedFactorial[n_,y_]:=If[n<0,Print["QDeformedFactorial[n,y] is defined only for n>=0"],
		If[n==0,1,(y^(2n)-1)/(y^2-1)QDeformedFactorial[n-1,y]]];

EvalQFact[f_]:=f/.{QFact[n_,y_]:>QDeformedFactorial[n,y]};

StackInvariantToOmb[gam_,y_]:=Module[{Li,gcd},
	gcd=GCD@@gam;
	Li=Flatten[Map[Permutations,ListAllPartitions[{gcd}]],1];
	-(y-1/y)Sum[Product[-Omb[gam Li[[i,j,1]]/gcd,y]/(y-1/y),{j,Length[Li[[i]]]}]/Length[Li[[i]]]!,{i,Length[Li]}]
];

HiggsGToOmb[f_]:=f/.{HiggsG[gam_,y_]:>Module[{Li,gcd},
	gcd=GCD@@gam;
	Li=Flatten[Map[Permutations,ListAllPartitions[{gcd}]],1];
	Sum[(-1)^(Length[Li[[i]]]-1)Product[Omb[gam Li[[i,j,1]]/gcd,y],{j,Length[Li[[i]]]}]/Length[Li[[i]]]!/(y-1/y)^(Length[Li[[i]]]-1),
	{i,Length[Li]}]]};

OmbToHiggsG[f_]:=f/.{Omb[gam_,y_]:>Module[{Li,gcd},
	gcd=GCD@@gam;
	Li=Flatten[Map[Permutations,ListAllPartitions[{gcd}]],1];
	Sum[
	   Product[HiggsG[gam Li[[i,j,1]]/gcd,y],{j,Length[Li[[i]]]}]/Length[Li[[i]]]/(y-1/y)^(Length[Li[[i]]]-1),
	{i,Length[Li]}]]};

HiggsGToOmb[Cvec_,f_]:=f/.{HiggsG[gam_,y_]:>Module[{Li,ListAllPart,ListAllSamePhase},
	ListAllPart=ListAllPartitions[gam];
ListAllSamePhase=Table[Length[Union[Map[Cvec #&,ListAllPart[[i]]]]]==1,{i,Length[ListAllPart]}];
	Li=Flatten[Map[Permutations,Pick[ListAllPart,ListAllSamePhase]],1];
Sum[(-1)^(Length[Li[[i]]]-1)Product[Omb[Li[[i,j]],y],{j,Length[Li[[i]]]}]/Length[Li[[i]]]!/(y-1/y)^(Length[Li[[i]]]-1),
	{i,Length[Li]}]]};

OmbToHiggsG[Cvec_,f_]:=f/.{Omb[gam_,y_]:>Module[{Li,ListAllPart,ListAllSamePhase},
		ListAllPart=ListAllPartitions[gam];
ListAllSamePhase=Table[Length[Union[Map[Cvec #&,ListAllPart[[i]]]]]==1,{i,Length[ListAllPart]}];
	Li=Flatten[Map[Permutations,Pick[ListAllPart,ListAllSamePhase]],1];
	Sum[
	   Product[HiggsG[Li[[i,j]],y],{j,Length[Li[[i]]]}]/Length[Li[[i]]]/(y-1/y)^(Length[Li[[i]]]-1),
	{i,Length[Li]}]]};

EvalHiggsG[Mat_,Cvec_,f_]:=f/.{HiggsG[gam_,y_]:>StackInvariant[Mat,Cvec,gam,y]};

EvalHiggsGGen[Mat_,Cvec_,f_]:=f/.{HiggsG[gam_,y_]:>StackInvariantGen[Mat,Cvec,gam,y]};

EvalHiggsg[Mat_,Cvec_,f_]:=f/.{Higgsg[Li_,y_]:>AbelianStackInvariant[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]};

StackInvariantGen[Mat_,Cvec_,Nvec_,y_]:=Module[{m,JKListAllPermutations,pa,Cvec0,Eu},
  (* differs from StackInvariant by y\[Rule]1/y ! *)
  m=Length[Nvec];
  If[Max[Nvec]<0,Print["StackInvariantGen: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  (* If[Plus@@Nvec==1,Return[1]]; *)
  Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  pa=Flatten[Map[Permutations,ListAllPartitions[Nvec]],1];
  If[$QuiverVerbose,
    If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
        Print["StackInvariantGen: Length of DSZ matrix, FI and dimension vectors do not match !"]];
    If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,
		Print["StackInvariantGen: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0];
    ];   
  PrintTemporary["StackInvariantGen: summing ", Length[pa]," ordered partitions"];
  ];
    Eu=EulerForm[Mat];
(1/y-y) (-y)^(Sum[Eu[[k,l]] Nvec[[k]] Nvec[[l]],{k,m},{l,m}])
	Sum[If[(Length[pa[[i]]]==1) ||And@@Table[Sum[Cvec0[[k]] pa[[i,a,k]],{a,b},{k,m}]>0,{b,Length[pa[[i]]]-1}],
      (-1)^(Length[pa[[i]]]-1)
       y^(-2  Sum[ Eu[[l,k]] pa[[i,a,k]]pa[[i,b,l]],
    {a,1,Length[pa[[i]]]},{b,a,Length[pa[[i]]]},{k,m},{l,m}])/
    Product[(1-y^(-2 l)),{j,1,Length[pa[[i]]]},{k,m},{l,1,pa[[i,j,k]]}],0],{i,Length[pa]}]
];

EulerForm[Mat_]:=Table[If[k==l,1,0]-QuiverMultiplierMat[k,l] Max[Mat[[k,l]],0],{k,Length[Mat]},{l,Length[Mat]}];

SubVectors[Nvec_]:=Module[{Li},If[Length[Nvec]<=1,Table[{i},{i,0,Nvec[[1]]}],
Li=SubVectors[Drop[Nvec,1]];
Flatten[Table[Flatten[{i,Li[[j]]}],{i,0,Nvec[[1]]},{j,Length[Li]}],1]]];

StackInvariantFast[Mat_,Cvec_,Nvec_,y_]:=Module[{Eu,Li,Cvec0,ReinekeMatrix}, 
  If[Max[Nvec]<0,Print["StackInvariantFast: The dimension vector must be positive !"]];
       If[Plus@@Nvec==0,Return[0]]; If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
Print["StackInvariantFast: Length of DSZ matrix, FI and dimension vectors do not match !"]];
Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
Eu=EulerForm[Mat];
If[$QuiverVerbose,
          If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,
		Print["StackInvariantFast: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0];
    ]];   
Li=Union[Flatten[{{Nvec},{ConstantArray[0,Length[Nvec]]},Select[SubVectors[Nvec],#.Cvec0>0 &]},1]];
ReinekeMatrix=Table[If[i==j,1,If[Max[Li[[i]]-Li[[j]]]<=0,(-y)^(-Li[[i]].(Transpose[Eu]-Eu).Li[[j]]-(Li[[j]]-Li[[i]]).Eu.(Li[[j]]-Li[[i]]))/
Product[1-y^(-2l),{k,Length[Nvec]},{l,1,Li[[j,k]]-Li[[i,k]]}]
,0]],{i,Length[Li]},{j,Length[Li]}];
If[$QuiverVerbose,PrintTemporary["StackInvariantFast: Inverting matrix of size ",Length[Li]]];
(y-1/y)Inverse[ReinekeMatrix][[1,Length[Li]]]
];

EvalReinekeIndex[Mat_,Cvec_,f_]:=f/.{Coulombg[Li_,y_]:>ReinekeIndex[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]};

ReinekeIndex[Mat_,Cvec_,y_]:=Module[{m,RCvec},
m=Length[Cvec];
 If[(Abs[Plus@@(Cvec)]>$QuiverPrecision),       
		Print["ReinekeIndex: FI terms do not sum up to zero"]] ;
RCvec=1/1000/$QuiverPerturb2 Table[Random[Integer,{1,1000}]/1000,{i,m}];
	RCvec[[m]]=-Sum[RCvec[[i]],{i,m-1}];
EvalQFact[AbelianStackInvariant[Mat,Cvec+RCvec,y]]
];


(* ::Section:: *)
(*Mutations*)


(* MutateRight[{Mat_,Cvec_,Nvec_},k_]:=Module[{m},
  m=Length[Mat];
{Table[If[(i==k)||(j==k),-Mat[[i,j]],Mat[[i,j]]+$QuiverMutationMult Max[0,Mat[[i,k]] Mat[[k,j]]] Sign[Mat[[k,j]]]],{i,m},{j,m}],
 Table[If[i==k,-Cvec[[i]],Cvec[[i]]+$QuiverMutationMult Max[0,Mat[[i,k]]] Cvec[[k]]],{i,m}],
 Table[If[i==k,-Nvec[[i]]+Sum[Nvec[[j]] $QuiverMutationMult Max[0,Mat[[j,k]]],{j,m}],Nvec[[i]]],{i,m}]}];

MutateLeft[{Mat_,Cvec_,Nvec_},k_]:=Module[{m},
  m=Length[Mat];
{Table[If[(i==k)||(j==k),-Mat[[i,j]],Mat[[i,j]]+$QuiverMutationMult Max[0,Mat[[i,k]] Mat[[k,j]]] Sign[Mat[[k,j]]]],{i,m},{j,m}],
 Table[If[i==k,-Cvec[[i]],Cvec[[i]]+$QuiverMutationMult Max[0,-Mat[[i,k]]] Cvec[[k]]],{i,m}],   
 Table[If[i==k,-Nvec[[i]]+Sum[Nvec[[j]] $QuiverMutationMult Max[0,-Mat[[j,k]]],{j,m}],Nvec[[i]]],{i,m}]}];

MutateRightList[Mat_,Cvec_,Nvec_,klist_]:=Module[{m,Mat2,Cvec2,Nvec2,k},
  If[Length[klist]>1,
    {Mat2,Cvec2,Nvec2}=MutateRightList[Mat,Cvec,Nvec,Drop[klist,-1]]; 
       k=Last[klist];,
    {Mat2,Cvec2,Nvec2}={Mat,Cvec,Nvec};
       k=klist[[1]];
  ];
  m=Length[Mat2];
  {Table[If[(i==k)||(j==k),-Mat2[[i,j]],Mat2[[i,j]]+$QuiverMutationMult Max[0,Mat2[[i,k]] Mat2[[k,j]]] Sign[Mat2[[k,j]]]],{i,m},{j,m}],
   Table[If[i==k,-Cvec2[[i]],Cvec2[[i]]+$QuiverMutationMult Max[0,Mat2[[i,k]]] Cvec2[[k]]],{i,m}],
   Table[If[i==k,-Nvec2[[i]]+Sum[Nvec2[[j]] $QuiverMutationMult Max[0,Mat2[[j,k]]],{j,m}],Nvec2[[i]]],{i,m}]}];
*)

Mutate[Mat_,klist_]:=Module[{m,Mat2,k},
  Which[Length[klist]>1,
    Mat2=Mutate[Mat,Drop[klist,-1]]; k=Last[klist];,
	Length[klist]==1,  Mat2=Mat; k=klist[[1]],
    Length[klist]==0,  Mat2=Mat; k=klist;
 ];
  m=Length[Mat2]; 
Table[If[(i==k)||(j==k),-Mat2[[i,j]],Mat2[[i,j]]+$QuiverMutationMult Max[0,Mat2[[i,k]] Mat2[[k,j]]] Sign[Mat2[[k,j]]]],{i,m},{j,m}]
];

MutateRight[Mat_,Cvec_,Nvec_,klist_]:=Module[{m,Mat2,Cvec2,Nvec2,k},
  Which[Length[klist]>1,
    {Mat2,Cvec2,Nvec2}=MutateRight[Mat,Cvec,Nvec,Drop[klist,-1]]; k=Last[klist];,
	Length[klist]==1,  {Mat2,Cvec2,Nvec2}={Mat,Cvec,Nvec}; k=klist[[1]],
    Length[klist]==0,  {Mat2,Cvec2,Nvec2}={Mat,Cvec,Nvec}; k=klist;
  ];
  m=Length[Mat2]; 
  {Table[If[(i==k)||(j==k),-Mat2[[i,j]],Mat2[[i,j]]+$QuiverMutationMult Max[0,Mat2[[i,k]] Mat2[[k,j]]] Sign[Mat2[[k,j]]]],{i,m},{j,m}],
   Table[If[i==k,-Cvec2[[i]],Cvec2[[i]]+$QuiverMutationMult Max[0,Mat2[[i,k]]] Cvec2[[k]]],{i,m}],
   Table[If[i==k,-Nvec2[[i]]+Sum[Nvec2[[j]] $QuiverMutationMult Max[0,Mat2[[j,k]]],{j,m}],Nvec2[[i]]],{i,m}]}
];

MutateLeft[Mat_,Cvec_,Nvec_,klist_]:=Module[{m,Mat2,Cvec2,Nvec2,k},
  Which[Length[klist]>1,
    {Mat2,Cvec2,Nvec2}=MutateLeft[Mat,Cvec,Nvec,Drop[klist,-1]]; k=Last[klist];,
	Length[klist]==1,  {Mat2,Cvec2,Nvec2}={Mat,Cvec,Nvec}; k=klist[[1]],
    Length[klist]==0,  {Mat2,Cvec2,Nvec2}={Mat,Cvec,Nvec}; k=klist;
  ];
  m=Length[Mat2]; 
  {Table[If[(i==k)||(j==k),-Mat2[[i,j]],Mat2[[i,j]]+$QuiverMutationMult Max[0,Mat2[[i,k]] Mat2[[k,j]]] Sign[Mat2[[k,j]]]],{i,m},{j,m}],
   Table[If[i==k,-Cvec2[[i]],Cvec2[[i]]+$QuiverMutationMult Max[0,-Mat2[[i,k]]] Cvec2[[k]]],{i,m}],
   Table[If[i==k,-Nvec2[[i]]+Sum[Nvec2[[j]] $QuiverMutationMult Max[0,-Mat2[[j,k]]],{j,m}],Nvec2[[i]]],{i,m}]}
];

MutateRightOmS[Mat_,k_,f_]:=f/.OmS[Nvec_,y___]:>
     If[Nvec==Table[If[i==k,Nvec[[k]],0],{i,Length[Mat]}],OmS2[Nvec,y],
     OmS2[Table[If[i==k,-Nvec[[i]]
      +$QuiverMutationMult Sum[Nvec[[j]] Max[0,Mat[[j,k]]],{j,Length[Mat]}]
      -$QuiverMutationMult Max[0,Sum[Nvec[[j]]Mat[[j,k]],{j,Length[Mat]}]],Nvec[[i]]],
         {i,Length[Mat]}],y]];

OmSToOmS2[f_]:=f/. OmS[gam__]:>OmS2[gam];

MutateRightOmS2[Mat_,k_,f_]:=f/.OmS2[Nvec_,y___]:>
     If[Nvec==Table[If[i==k,Nvec[[k]],0],{i,Length[Mat]}],OmS[Nvec,y],
     OmS[Table[If[i==k,-Nvec[[i]]
      +$QuiverMutationMult Sum[Nvec[[j]] Max[0,Mat[[j,k]]],{j,Length[Mat]}]
      -$QuiverMutationMult Max[0,Sum[Nvec[[j]]Mat[[j,k]],{j,Length[Mat]}]],Nvec[[i]]],
         {i,Length[Mat]}],y]];

MutateLeftOmS[Mat_,k_,f_]:=f/.OmS[Nvec_,y___]:>
     If[Nvec==Table[If[i==k,Nvec[[k]],0],{i,Length[Mat]}],OmS2[Nvec,y],
     OmS2[Table[If[i==k,-Nvec[[i]]
      +$QuiverMutationMult Sum[Nvec[[j]] Max[0,-Mat[[j,k]]],{j,Length[Mat]}]
      -$QuiverMutationMult Max[0,-Sum[Nvec[[j]]Mat[[j,k]],{j,Length[Mat]}]],Nvec[[i]]],
         {i,Length[Mat]}],y]];

MutateLeftOmS2[Mat_,k_,f_]:=f/.OmS2[Nvec_,y___]:>
     If[Nvec==Table[If[i==k,Nvec[[k]],0],{i,Length[Mat]}],OmS[Nvec,y],
     OmS[Table[If[i==k,-Nvec[[i]]
      +$QuiverMutationMult Sum[Nvec[[j]] Max[0,-Mat[[j,k]]],{j,Length[Mat]}]
      -$QuiverMutationMult Max[0,-Sum[Nvec[[j]]Mat[[j,k]],{j,Length[Mat]}]],Nvec[[i]]],
         {i,Length[Mat]}],y]];

DropOmSNeg[f_]:= f /.{OmS[gam_,t___]:>0 /;Min[gam]<0, OmS2[gam_,t___]:>0 /;Min[gam]<0};

CompareDSZMatrices[Mat1_,Mat2_]:=Module[{LiPerm,Li},
Li={};
If[Length[Mat1]!=Length[Mat2],Print["CompareDSZMatrices: The two matrices do not have the same size !"];
{},
If[Sort[Tally[Flatten[Mat2]]]!=Sort[Tally[Flatten[Mat2]]],
Print["CompareDSZMatrices: The two matrices do not have the same unordered list of entries !"],
LiPerm=Permutations[Range[Length[Mat1]]];
Do[If[Mat1==Mat2[[LiPerm[[i]],LiPerm[[i]]]],AppendTo[Li,LiPerm[[i]]]],{i,Length[LiPerm]}]
]];
Li];


(* ::Section:: *)
(*Hua formula*)


PartitionWeight[pa_]:=Sum[i pa[[i]],{i,Length[pa]}];
PartitionPairing[pa1_,pa2_]:=Sum[Min[i,j]pa1[[i]]pa2[[j]],{i,Length[pa1]},{j,Length[pa2]}];
AllPartitions[d_]:=Module[{k},If[d==1,{{0},{1}},Drop[Union[Flatten[Table[If[Sum[i k[i],{i,d}]<=d,k/@Range[d],
          {}],##]&@@({k[#],0,d}&/@Range[d]),d-1]],1]]];
HuaTermMult[Mat_,ListPa_]:=Module[{i,j,k,l},Product[If[Mat[[k,l]]>0, 
    y^(2Mat[[k,l]] PartitionPairing[ListPa[[k]],ListPa[[l]]]),1]
    ,{k,Length[Mat]},{l,Length[Mat]}] Product[
    x[l]^(PartitionWeight[ListPa[[l]]])/y^(2PartitionPairing[ListPa[[l]],ListPa[[l]]])/Product[(1-y^(-2j)),{i,Length[ListPa[[l]]]},{j,ListPa[[l,i]]}],{l,Length[Mat]}]];
HuaFormula[Mat_,Nvec_]:=Module[{Li,HuaSum,LogHuaSum,t,k,m},
  Li=Table[AllPartitions[Nvec[[i]]],{i,Length[Nvec]}];
  HuaSum=Sum[HuaTermMult[Mat,Table[Li[[i,m[i]]],{i,Length[Mat]}]],##]&@@
              ({m[#],Length[Li[[#]]]}&/@Range[Length[Mat]]);
  LogHuaSum=Expand[Normal[Expand[Series[Log[HuaSum]/.x[i_]->t x[i],{t,0,Plus@@Nvec}]]
              /.{x[i_]^p_:>0/;p>Nvec[[i]]}]]/.{x[i_]^p_:>0/;p>Nvec[[i]]};
  Normal[ExpandAll[Simplify[Series[(y^2-1)Sum[MoebiusMu[k]/k 
         (LogHuaSum/.{x[i_]->x[i]^k,y->y^k,t->t^k}/.{x[i_]^p_:>0/;p>Nvec[[i]]}),{k,1,Max[Nvec]}],{t,0,Plus@@Nvec}]]]]
  /.{x[i_]^p_:>0/;p>Nvec[[i]]}/.t->1];


(* ::Section:: *)
(*Jeffrey-Kirwan residue formula*)


(*JKInitialize[Nvec_,JKFrozenCartan_]:=Module[{},
(* construct a Mask with False on entries which are decoupled, True otherwise *)
JKFrozenMask=Flatten[Table[Table[If[Length[Position[JKFrozenCartan,{i,j}]]>0,False,True],{j,Nvec[[i]]}],{i,Length[Nvec]}]];
(* construct list of Cartan variables for each node, except decoupled ones *)
JKFrozenRuleEuler=Table[u[JKFrozenCartan[[i,1]],JKFrozenCartan[[i,2]]]->0,{i,Length[JKFrozenCartan]}];
JKFrozenRuleRational=Table[u[JKFrozenCartan[[i,1]],JKFrozenCartan[[i,2]]]->1,{i,Length[JKFrozenCartan]}];
(* u[i,ii] is the ii-th Cartan associated the i-th node *)JKListuAll=Flatten[Table[u[i,ii],{i,Length[Nvec]},{ii,Nvec[[i]]}]];
JKListu=Pick[JKListuAll,JKFrozenMask];
(*JKListut=JKListu/.{u[i_,j_]:>ut[i,j]};*)
JKListut=Table[ut[i],{i,Length[JKListu]}];
]; *)

JKInitialize[Mat_,RMat_,Cvec_,Nvec_]:=Module[{LiCoor},
JKFrozenCartan={{1,1}};
   (* construct a Mask with False on entries which are decoupled, True otherwise *)
JKFrozenMask=Flatten[Table[Table[If[Length[Position[JKFrozenCartan,{i,j}]]>0,False,True],{j,Nvec[[i]]}],{i,Length[Nvec]}]];
(* construct list of Cartan variables for each node, except decoupled ones *)
JKFrozenRuleEuler=Table[u[JKFrozenCartan[[i,1]],JKFrozenCartan[[i,2]]]->0,{i,Length[JKFrozenCartan]}];
JKFrozenRuleRational=Table[u[JKFrozenCartan[[i,1]],JKFrozenCartan[[i,2]]]->1,{i,Length[JKFrozenCartan]}];
(* u[i,ii] is the ii-th Cartan associated the i-th node *)JKListuAll=Flatten[Table[u[i,ii],{i,Length[Nvec]},{ii,Nvec[[i]]}]];
JKListuDisplay=JKListuAll;
JKListu=Pick[JKListuAll,JKFrozenMask];
(*JKListut=JKListu/.{u[i_,j_]:>ut[i,j]};*)
JKListut=Table[ut[i],{i,Length[JKListu]}];
(* construct Charge Matrix *)
JKChargeMatrix=ChargeMatrixFromQuiver[Mat,RMat,Nvec];
(* Construct perturbed stability vector *) 
JKEta=Flatten[Table[Table[Cvec[[i]],{j,Nvec[[i]]}],{i,Length[Mat]}]]+
1/1000/$QuiverPerturb2 Sort[Table[Random[Integer,{1,1000}],{i,Plus@@Nvec}]];
LiCoor=Flatten[Table[{i-1,(Nvec[[i]]-j)*(1-i/Length[Nvec]/4)},{i,Length[Nvec]},{j,Nvec[[i]]}],1];
JKVertexCoordinates=Table[i->LiCoor[[i]],{i,Length[LiCoor]}];
JKVertexLabels=Table[i->JKListuDisplay[[i]],{i,Length[LiCoor]}];
];

ZEuler[ChargeMatrix_,Nvec_]:= 1/Product[Nvec[[i]]!,{i,Length[Nvec]}]Product[If[ii==jj,1,-(u[i,ii]-u[i,jj])/ (u[i,ii]-u[i,jj]-1 )],{i,Length[Nvec]},{ii,Nvec[[i]]},{jj,Nvec[[i]]}]Product[(-((Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+(ChargeMatrix[[i,-2]]/2-1)))/((Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+ ChargeMatrix[[i,-2]]/2)))^ChargeMatrix[[i,-1]],{i,Length[ChargeMatrix]}];

ZRational[ChargeMatrix_,Nvec_]:=1/Product[Nvec[[i]]!,{i,Length[Nvec]}]/Product[u[i,ii],{i,Length[Nvec]},{ii,Nvec[[i]]}]Factor[Product[If[ii==jj,1,(-y(u[i,ii]-u[i,jj])/(u[i,ii]-y^2 u[i,jj]))],{i,Length[Nvec]},{ii,Nvec[[i]]},{jj,Nvec[[i]]}]Product[(-1/y(Times@@(JKListuAll^(Drop[ChargeMatrix[[i]],-2])) - y^(2-ChargeMatrix[[i,-2]]))/(Times@@(JKListuAll^(Drop[ChargeMatrix[[i]],-2])) -y^(-ChargeMatrix[[i,-2]])))^ChargeMatrix[[i,-1]],{i,Length[ChargeMatrix]}]]/(y-1/y)^(Plus@@Nvec-Length[JKFrozenCartan]); 

ZTrig[ChargeMatrix_,Nvec_]:= (2Pi I z)^(Plus@@Nvec-Length[JKFrozenCartan])/Product[Nvec[[i]]!,{i,Length[Nvec]}]Product[If[ii==jj,1,(-(Exp[Pi I z(u[i,ii]-u[i,jj])]-Exp[-Pi I z(u[i,ii]-u[i,jj])])/(Exp[Pi I z(u[i,ii]-u[i,jj]-1 )]-Exp[-Pi I z(u[i,ii]-u[i,jj]-1)]))],{i,Length[Nvec]},{ii,Nvec[[i]]},{jj,Nvec[[i]]}]Product[(-((Exp[Pi I z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+(ChargeMatrix[[i,-2]]/2-1))]-Exp[-Pi I z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+(ChargeMatrix[[i,-2]]/2-1))])/((Exp[Pi I z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+ ChargeMatrix[[i,-2]]/2)]-Exp[-Pi I z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+ ChargeMatrix[[i,-2]]/2)]))))^ChargeMatrix[[i,-1]],{i,Length[ChargeMatrix]}]/(Exp[Pi I z]-Exp[-Pi I z])^(Plus@@Nvec-Length[JKFrozenCartan]);

ZElliptic[ChargeMatrix_,Nvec_]:= Module[{},(2Pi Eta^3 z/Theta[z])^(Plus@@Nvec-Length[JKFrozenCartan])/Product[Nvec[[i]]!,{i,Length[Nvec]}]Product[If[ii==jj,1,-Theta[z(u[i,ii]-u[i,jj])]/Theta[z(u[i,ii]-u[i,jj]-1)]
],{i,Length[Nvec]},{ii,Nvec[[i]]},{jj,Nvec[[i]]}]Product[
(- Theta[z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+(ChargeMatrix[[i,-2]]/2-1))]/Theta[z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+ ChargeMatrix[[i,-2]]/2)])^ChargeMatrix[[i,-1]],{i,Length[ChargeMatrix]}]];

ZEulerPartial[ChargeMatrix_,Nvec_,ListPerm_]:= Product[ 
If[Length[ListPerm[[i]]]>0,
(* for split nodes *) 
Signature[ListPerm[[i]]]/Product[(u[i,ii]-u[i,ListPerm[[i,ii]]]+1),{ii,Nvec[[i]]}]
,(* for unsplit nodes *)
Product[If[ii==jj,1,-(u[i,ii]-u[i,jj])/ (u[i,ii]-u[i,jj]-1 )],{ii,Nvec[[i]]},{jj,Nvec[[i]]}]]/(Nvec[[i]]!),{i,Length[ListPerm]}]Product[(-((Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+(ChargeMatrix[[i,-2]]/2-1)))/((Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+ ChargeMatrix[[i,-2]]/2)))^ChargeMatrix[[i,-1]],{i,Length[ChargeMatrix]}] ;

ZRationalPartial[ChargeMatrix_,Nvec_,ListPerm_]:=Factor[Product[
If[Length[ListPerm[[i]]]>0,
(* for split nodes *) 
 (1-y^2)^Length[ListPerm[[i]]] Signature[ListPerm[[i]]]/
Product[u[i,ii]-y^2 u[i,ListPerm[[i,ii]]],{ii,Nvec[[i]]}],
(* for unsplit nodes *) 
1/Product[u[i,ii],{ii,Nvec[[i]]}]Product[If[ii==jj,1,(-y(u[i,ii]-u[i,jj])/(u[i,ii]-y^2 u[i,jj]))],{ii,Nvec[[i]]},{jj,Nvec[[i]]}]
]1/(Nvec[[i]]!),{i,Length[ListPerm]}]Product[(-1/y(Times@@(JKListuAll^(Drop[ChargeMatrix[[i]],-2])) - y^(2-ChargeMatrix[[i,-2]]))/(Times@@(JKListuAll^(Drop[ChargeMatrix[[i]],-2])) -y^(-ChargeMatrix[[i,-2]])))^ChargeMatrix[[i,-1]],{i,Length[ChargeMatrix]}]/(y-1/y)^(Plus@@Nvec-Length[JKFrozenCartan])]; 

ZTrigPartial[ChargeMatrix_,Nvec_,ListPerm_]:=Module[{},(2Pi I z)^(Plus@@Nvec-Length[JKFrozenCartan])Product[
If[Length[ListPerm[[i]]]>0,
(* for split nodes *) 
(-(Exp[I Pi z]-Exp[-I Pi z])/2/I)^Length[ListPerm[[i]]]Signature[ListPerm[[i]]]Product[2I/(Exp[Pi I z(u[i,ii]-u[i,ListPerm[[i,ii]]]-1)]-Exp[-Pi I z(u[i,ii]-u[i,ListPerm[[i,ii]]]-1)]),{ii,Length[ListPerm[[i]]]}],
Product[If[ii==jj,1,(-(Exp[Pi I z(u[i,ii]-u[i,jj])]-Exp[-Pi I z(u[i,ii]-u[i,jj])])/(Exp[Pi I z(u[i,ii]-u[i,jj]-1 )]-Exp[-Pi I z(u[i,ii]-u[i,jj]-1)]))],{i,Length[Nvec]},{ii,Nvec[[i]]},{jj,Nvec[[i]]}]
]/Nvec[[i]]!,{i,Length[Nvec]}]Product[(-((Exp[Pi I z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+(ChargeMatrix[[i,-2]]/2-1))]-Exp[-Pi I z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+(ChargeMatrix[[i,-2]]/2-1))])/((Exp[Pi I z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+ ChargeMatrix[[i,-2]]/2)]-Exp[-Pi I z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+ ChargeMatrix[[i,-2]]/2)]))))^ChargeMatrix[[i,-1]],{i,Length[ChargeMatrix]}]/(Exp[Pi I z]-Exp[-Pi I z])^(Plus@@Nvec-Length[JKFrozenCartan])];

ZEllipticPartial[ChargeMatrix_,Nvec_,ListPerm_]:=Module[{},(2Pi Eta^3 z/Theta[z])^(Plus@@Nvec-Length[JKFrozenCartan])
   Product[If[Length[ListPerm[[i]]]>0,
(* for split nodes *)
(-Theta[z]/2)^Nvec[[i]]   Signature[ListPerm[[i]]]
      Product[2/Theta[z( u[i,ii]-u[i,ListPerm[[i,ii]]]-1)] ,{ii,Nvec[[i]]}],
(* for unsplit nodes *)
Product[If[ii==jj,1,-Theta[z(u[i,ii]-u[i,jj])]/Theta[z(u[i,ii]-u[i,jj]-1)]],{ii,Nvec[[i]]},{jj,Nvec[[i]]}]
]/Nvec[[i]]!,{i,Length[Nvec]}]  
Product[
(-Theta[z(Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+(ChargeMatrix[[i,-2]]/2-1))]/Theta[z (Sum[ChargeMatrix[[i,j]]JKListuAll[[j]],{j,Length[JKListuAll]}]+ ChargeMatrix[[i,-2]]/2)])^ChargeMatrix[[i,-1]]
     ,{i,Length[ChargeMatrix]}]];
     
JKResidueRational[StableFlag_,ZRational_]:=Module[{Inter,QT,QTi,Ksign,QTu,QTut,repu,gt,i,j},
(* StableFlag is a list  {inter,{hyperplanes},QT,Kab} *)
Inter=StableFlag[[1]];
  QT=StableFlag[[3]]; QTi=Inverse[QT];
  Ksign=Sign[Det[StableFlag[[4]]]];
  QTut=y^(2 Inter)(*Exp[2Pi I Inter/.z->0]*) Table[Product[ JKListut[[j]]^QTi[[i,j]],{j,Length[JKListut]}],{i,Length[JKListut]}];
repu=Table[JKListu[[i]]->QTut[[i]],{i,Length[JKListu]}];
gt=Factor[(ZRational/.repu) ((Product[JKListu[[i]],{i,Length[JKListu]}]/.repu)/Product[JKListut[[i]],{i,Length[JKListut]}])/ Det[QT]/.JKFrozenRuleRational];
 If[$QuiverVerbose,PrintTemporary["JKResidueRational: Step ",Dynamic[i],"/",Length[JKListut]]];
 Do[
gt=ResidueFast[gt,{JKListut[[i]],1}],{i,Length[JKListut]}];
 Ksign  gt];

JKResidueTrig[StableFlag_,ZTrig_]:=Module[{Inter,QT,QTi,Ksign,repu,gt,i,j}, 
Inter=StableFlag[[1]]; 
  QT=StableFlag[[3]]; QTi=Inverse[QT];
  Ksign=Sign[Det[StableFlag[[4]]]];
repu=Table[JKListu[[i]]->(Inverse[QT].JKListut+Inter)[[i]],{i,Length[JKListu]}];
gt=(ZTrig/.repu)/Det[QT] /.JKFrozenRuleEuler;
If[$QuiverVerbose,PrintTemporary["JKResidueTrig: Step ",Dynamic[i],"/",Length[JKListut]]];
Do[
gt=ResidueFast[gt,{JKListut[[i]], 0}],{i,Length[JKListut]}];
 Ksign  gt];

(* one multiplicity-1 hyperplane for each chiral multiplet; RMat[[i,j]] is now a vector *)
ChargeMatrixFromQuiver[Mat_,RMat_,Nvec_]:=Select[Flatten[ 
Table[If[Mat[[i,j]]>0,If[Length[RMat[[i,j]]]==0,Flatten[Table[Flatten[{LegCharge[Nvec,{i,ii},{j,jj}],RMat[[i,j]],Mat[[i,j]]}],{ii,Nvec[[i]]},{jj,Nvec[[j]]}],1],
Flatten[Table[Flatten[{LegCharge[Nvec,{i,ii},{j,jj}],RMat[[i,j,k]],1}],{ii,Nvec[[i]]},{jj,Nvec[[j]]},{k,Mat[[i,j]]}],2]],{}],{i,Length[Mat]},{j,Length[Mat]}] ,2],Length[#]>0&];

CompleteChargeMatrix[ChargeMatrix_,Nvec_]:= Select[Flatten[
{{ChargeMatrix},Flatten[Table[Map[Flatten,{{LegCharge[Nvec,{i,ii},{i,jj}],-2,1},{LegCharge[Nvec,{i,jj},{i,ii}],-2,1}}],{i,Length[Nvec]},{ii,Nvec[[i]]},{jj,ii+1,Nvec[[i]]}],2]},2],Length[#]>0&];

CompleteChargeNumMatrix[ChargeMatrix_,Nvec_]:= Select[Flatten[
{{ChargeMatrix},Flatten[Table[Map[Flatten,{{LegCharge[Nvec,{i,ii},{i,jj}],0,1},{LegCharge[Nvec,{i,jj},{i,ii}],0,1}}],{i,Length[Nvec]},{ii,Nvec[[i]]},{jj,ii+1,Nvec[[i]]}],2]},2],Length[#]>0&];

PartialChargeMatrix[ChargeMatrix_,Nvec_,perm_]:= 
Join@@Flatten[{{ChargeMatrix},
(* for each node, add vector multiplet charges: *)
Select[Table[
If[Length[perm[[i]]]==0,
(* in absence of perm for node i, include all vectors, R-charge=-2 *)Flatten[Table[{Flatten[{LegCharge[Nvec,{i,ii},{i,jj}],-2,1}],Flatten[{LegCharge[Nvec,{i,jj},{i,ii}],-2,1}]},{ii,Nvec[[i]]},{jj,ii+1,Nvec[[i]]}],2]
,
(* if a perm for node i is specified, only consecutive vectors *)
Select[Table[If[perm[[i,ii]]==ii,{},Flatten[{LegCharge[Nvec,{i,ii},{i,perm[[i,ii]]}],-2,1}]],{ii,Nvec[[i]]}],Length[#]>0&]],{i,Length[Nvec]}],Length[#]>0&]
},1];

PartialChargeNumMatrix[ChargeMatrix_,Nvec_,perm_]:= 
Join@@Flatten[{{ChargeMatrix},
(* for each node, add vector multiplet charges: *)
Select[Table[
If[Length[perm[[i]]]==0,
(* in absence of perm for node i, include all vectors, R-charge=0  *)Flatten[Table[{Flatten[{LegCharge[Nvec,{i,ii},{i,jj}],0,1}],Flatten[{LegCharge[Nvec,{i,jj},{i,ii}],0,1}]},{ii,Nvec[[i]]},{jj,ii+1,Nvec[[i]]}],2]
,
(* if a perm for node i is specified, no numerator *)
{}],{i,Length[Nvec]}],Length[#]>0&]
},1];
LegCharge[Nvec_,{i_,ii_},{j_,jj_}]:=Module[{k,kk},Flatten[Table[If[{k,kk}=={i,ii},1,If[{k,kk}=={j,jj},-1,0]],{k,Length[Nvec]},{kk,Nvec[[k]]}]]];

TrimChargeTable[Sing_]:=Map[Pick[#,Flatten[{JKFrozenMask,False,False}]]&,Sing];
(* two flags are equivalent if Q2.Inverse[Q1] is lower triangular *)

FindIntersection[Sing_]:=Module[{QT,Rvec,i,d,so0,so1},
  QT=TrimChargeTable[Sing];
  d=Abs[Det[QT]];
  Rvec=Table[Sing[[i,-2]],{i,Length[Sing]}];
  If[d==0,(*Print["Degenerate intersection"];*)
   {},
  If[d==1,
  (JKListu/.Solve[QT.JKListu+Rvec/2==0,JKListu])
  ,Print["Two hyperplanes intersect more than once !"];
 (* inhomogenous solution *)
  so0=Solve[QT.JKListu+Rvec/2==0,JKListu];
 (* homogeneous solution mod Det *)
so1=Select[Flatten[Table[If[Mod[QT.JKListu,d]==ConstantArray[0,Length[JKListu]],JKListu,{}],##]&@@Table[{JKListu[[i]],0,d-1},{i,Length[JKListu]}],Length[JKListu]-1],Length[#]>0&];
Flatten[Table[(JKListu/.so0[[1]])+(so1[[i]]+tau so1[[j]])/d,{i,Length[so1]},{j,Length[so1]}],1]]
]];

FlagToHyperplanes[Sing_]:=Module[{QT,Rvec},
Rvec=Table[Sing[[i,-2]],{i,Length[Sing]}];
QT=Map[Drop[#,-2]&,Sing];
QT.JKListuDisplay+ Rvec/2];

PartitionToPermutation[pa_]:=Module[{perm={},i=1,ta,mul},Do[AppendTo[perm,Range[i,i+pa[[j]]-1]];i=i+pa[[j]],{j,Length[pa]}];
 PermutationList[Cycles[perm],Plus@@pa]];

(* reverse operation *)
PermutationToPartition[perm_]:=Module[{li},
li=Map[Length,List@@PermutationCycles[perm][[1]]];
Join[li,ConstantArray[1,Length[perm]-Plus@@li]]
];

AbelianSubQuiver[Mat_,RMat_,Cvec_,Nvec_,perm_]:=Module[{Li},
Li=Map[PermutationToPartition,perm];
SubDSZ[Mat,RMat,Cvec,Flatten[Table[ArrayPad[{Li[[i,j]]},{i-1,Length[Nvec]-i}],{i,Length[Li]},{j,Length[Li[[i]]]}],1]]
];

(* symmetry factor for a given cycle shape *)
PartitionMultiplicity[pa_]:=Module[{ta=Tally[pa]},Factorial[Plus@@pa]/Product[ta[[i,1]]^ta[[i,2]] ta[[i,2]]!,{i,Length[ta]}]];

(* Constructs list of partitions at each node, represented by standard permutation, along with multiplicity *)
ListPermutationsWithMultiplicity[Nvec_]:=Module[{ListPermEachNode,ListPm,k,JKListAllPerms},ListPermEachNode=Table[Map[PartitionToPermutation,IntegerPartitions[Nvec[[i]]]],{i,Length[Nvec]}];
JKListAllPerms=Flatten[Table[ListPm[#,k[#]]& /@Range[Length[Nvec]],##]& @@({k[#],1,Length[ListPermEachNode[[#]]]}&/@Range[Length[Nvec]]),Length[Nvec]-1]/.ListPm[i_,j_]:>ListPermEachNode[[i,j]];
Table[{JKListAllPerms[[i]],Product[PartitionMultiplicity[PermutationToPartition[JKListAllPerms[[i,j]]]],{j,Length[JKListAllPerms[[i]]]}]},{i,Length[JKListAllPerms]}]
];

ListHyperplanesIntersectingAt[ListSings_,Inter_]:=ListSings[[Position[ListSings,Inter,2][[1,1]],2]];

TestProjectiveIntersection[ListSings_,Inter_]:=Module[{QT},
QT=TrimChargeTable[ListHyperplanesIntersectingAt[ListSings,Inter]];
If[Length[FindInstance[Min[QT.JKListu]>0,JKListu]]==0,False,True]];

(* collect hyperplanes which intersect at the point Inter *)
CollectHyperplanes[ListInterrplets_,Inter_]:=Module[{Li,ListInter},
ListInter=First[Transpose[ListInterrplets]];
Li=Flatten[Transpose[Position[ListInter,Inter]][[1]]];
Union[Flatten[Table[ListInterrplets[[Li[[i]],2]],{i,Length[Li]}],1]]
];

SameFlagQ[Q1_,Q2_]:=Module[{i,j,Q3},Q3=Q2.Inverse[Q1];Union[Flatten[Table[Q3[[i,j]],{i,1,Length[Q3]-1},{j,i+1,Length[Q3]}]]]]=={0};

FindSingularities[ChargeMatrix_]:=Module[{Listrplets,ListInterrplets,ListInterDistinct,ListSings},
If[Length[ChargeMatrix]>0,(* list of all r-plets of hyperplanes *)
Listrplets=Subsets[ChargeMatrix,{Length[ChargeMatrix[[1]]]-2-Length[JKFrozenCartan]}];
ListInterrplets=Select[Table[{FindIntersection[Listrplets[[l]]],Listrplets[[l]]},{l,Length[Listrplets]}],Length[#[[1]]]>0&];
  (* extract distinct intersection points *)
ListInterDistinct=DeleteDuplicates[Flatten[First[Transpose[ListInterrplets]],1]];
(* list all distinct intersections along with hyperplanes meeting at that point *)
ListSings=Table[{ListInterDistinct[[i]],CollectHyperplanes[ListInterrplets,ListInterDistinct[[i]]]},{i,Length[ListInterDistinct]}],{}]
(*PrintTemporary[Length[ListSings]," distinct intersections"];*)
];

FindStableFlags[Inter_,ListHyper_,Nvec_,Etavec_]:=
(* produce list of inter, hyperplanes, F, kappa matrices *)Module[{ListSubsets,ListFlags,ListDistinctFlags,ListStableFlags,ListCharges,QT,KTab},
ListCharges=TrimChargeTable[ListHyper];
(* produce the list of unordered r-tuplets *)ListSubsets=Subsets[ListHyper,{Plus@@Nvec-Length[JKFrozenCartan]}];
     ListStableFlags=
     Select[Flatten[Table[
        If[Det[TrimChargeTable[ListSubsets[[k]]]]==0,{},
      (* construct all ordered r-tuplet *)
        ListFlags=Permutations[ListSubsets[[k]]];
Select[Table[
QT=TrimChargeTable[ListFlags[[j]]];
KTab=Table[Sum[If[MatrixRank[Flatten[{Take[QT,r],{ListCharges[[i]]}},1]]==r,(* charge belongs to r-th graded component *) ListCharges[[i]],ConstantArray[0,Length[QT]]],{i,Length[ListCharges]}],{r,Length[QT]}];
If[Det[KTab]!=0,
 If[Min[Pick[Etavec,JKFrozenMask].Inverse[KTab]]>=0,
{Inter,ListFlags[[j]],QT,KTab},{}],{}],
{j,Length[ListFlags]}], Length[#]>0&]],
{k,Length[ListSubsets]}],1], Length[#]>0&];
ListDistinctFlags=DeleteDuplicates[ListStableFlags,SameFlagQ[#1[[3]],#2[[3]]]&];
ListDistinctFlags
];

TestStableFlag[ListHyper_,Flag_,Etavec_]:=Module[{QT,ListCharges,KTab},
QT=TrimChargeTable[Flag];
ListCharges=TrimChargeTable[ListHyper];
(*Print["Testing stability of ",Flag," ,QT=",QT," ,List=",ListCharges];*)
(* construct the kappa matrix *) 
KTab=Table[Sum[If[MatrixRank[Flatten[{Take[QT,r],{ListCharges[[i]]}},1]]==r,(* charge belongs to r-th graded component *) ListCharges[[i]],ConstantArray[0,Length[QT]]],{i,Length[ListCharges]}],{r,Length[QT]}];
If[Det[KTab]==0,0,
         If[Min[Pick[Etavec,JKFrozenMask].Inverse[KTab]]>=0,
Sign[Det[KTab]],0]]
];

FindStableDomains[Inter_,ListHyper_,Nvec_,Etavec_]:=Module[{ListSubsets,ListFlags,ListDistinctFlags,ListStableFlags,ListCharges,QT,KTab},
ListCharges=TrimChargeTable[ListHyper];
(* produce the list of unordered r-tuplets *)ListSubsets=Subsets[ListHyper,{Plus@@Nvec-Length[JKFrozenCartan]}];
     ListStableFlags=
     Select[Flatten[Table[
        If[Det[TrimChargeTable[ListSubsets[[k]]]]==0,{},
      (* construct all ordered r-tuplet *)
        ListFlags=Permutations[ListSubsets[[k]]];
Select[Table[
QT=TrimChargeTable[ListFlags[[j]]];
KTab=Table[Sum[If[MatrixRank[Flatten[{Take[QT,r],{ListCharges[[i]]}},1]]==r,(* charge belongs to r-th graded component *) ListCharges[[i]],ConstantArray[0,Length[QT]]],{i,Length[ListCharges]}],{r,Length[QT]}];
If[Det[KTab]!=0,
{Inter, QT, KTab , (*ListFlags[[j]],*) FlagToHyperplanes[ListFlags[[j]]],Sign[Det[KTab]],Reduce[And@@Map[#>0&,Pick[Etavec,JKFrozenMask].Inverse[KTab]]]},{}],
{j,Length[ListFlags]}], Length[#]>0&]],
{k,Length[ListSubsets]}],1], Length[#]>0&];
(*ListDistinctFlags=DeleteDuplicates[ListStableFlags,SameFlagQ[#1[[3]],#2[[3]]]&]; *)
ListDistinctFlags=ListStableFlags;
ListDistinctFlags
];

FindDegrees[ListSings_,NumSing_]:=Module[{NumHyperplanes,ListVanishingHyperplanes},
If[Length[NumSing]>0&&Length[ListSings]>0,NumHyperplanes=TrimChargeTable[NumSing].JKListu+z Table[NumSing[[i,-2]]/2,{i,Length[NumSing]}];
Table[
ListVanishingHyperplanes=Flatten[Position[NumHyperplanes/.Table[JKListu[[j]]->ListSings[[i,1,j]],{j,Length[JKListu]}],0]];
{ListSings[[i,1]],Plus@@Flatten[{Last/@ListSings[[i,2]],-(Last[NumSing[[#]]]&)/@ListVanishingHyperplanes}]},{i,Length[ListSings]}],{}]
];

FindMultiDegree[ListSings_,NumSing_,Inter_,StableFlag_]:=Module[{DenomSing,QT,repu,reput,DenomHyperplanes,NumHyperplanes,ListVanishingHyperplanesDenom,ListVanishingHyperplanesNum,SingIndex},
SingIndex=Position[Map[First,ListSings],Inter][[1,1]];
DenomSing=ListSings[[SingIndex,2]];
DenomHyperplanes=TrimChargeTable[DenomSing].JKListu+z Table[DenomSing[[i,-2]]/2,{i,Length[DenomSing]}];
NumHyperplanes=TrimChargeTable[NumSing].JKListu+z Table[NumSing[[i,-2]]/2,{i,Length[NumSing]}];
QT=TrimChargeTable[StableFlag];repu=Table[JKListu[[i]]->(Inverse[QT].JKListut+Inter)[[i]],{i,Length[JKListu]}];
Table[
ListVanishingHyperplanesDenom=Flatten[Position[Expand[DenomHyperplanes/.repu/.Table[JKListut[[j]]->0,{j,1,i}]],0]]; 
ListVanishingHyperplanesNum=Flatten[Position[Expand[NumHyperplanes/.repu/.Table[JKListut[[j]]->0,{j,1,i}]],0]]; 
Plus@@Flatten[{((Last[DenomSing[[#]]]&)/@ListVanishingHyperplanesDenom),-((Last[NumSing[[#]]]&)/@ListVanishingHyperplanesNum)}],{i,Length[JKListut]}]
];

DisplayFlagListDegrees[ListSings_,NumSing_,ListFlags_]:=Module[{},
If[Length[NumSing]>0&&Length[ListSings]>0,Print["- List of (intersection point, stable flag, sign, multidegree)"];
Print[Table[{
ListFlags[[i,1]],
FlagToHyperplanes[ListFlags[[i,2]]],
Sign[Det[ListFlags[[i,4]]]],FindMultiDegree[ListSings,NumSing,ListFlags[[i,1]],ListFlags[[i,2]]]},{i,Length[ListFlags]}]//MatrixForm]]];

DisplayFlagList[ListFlags_]:=Module[{},
Print["- List of (intersection point, stable flag, sign)"];
Print[Table[{
ListFlags[[i,1]],
FlagToHyperplanes[ListFlags[[i,2]]],
Sign[Det[ListFlags[[i,4]]]]
},{i,Length[ListFlags]}]//MatrixForm]];

DisplaySingList[ListSings_]:=Module[{},
Print["- List of (intersection point, hyperplanes meeting at that point, projective test):"];
Print[Table[{
ListSings[[i,1]],
FlagToHyperplanes[ListSings[[i,2]]],
TestProjectiveIntersection[ListSings,ListSings[[i,1]]] 
},{i,Length[ListSings]}]//MatrixForm]];

DisplayFlagTree[Fl_]:=Module[{LiArrows},
LiArrows=Table[{(Position[Drop[Fl[[2,i]],-2],1][[1,1]]),Position[Drop[Fl[[2,i]],-2],-1][[1,1]],1/2Take[Fl[[2,i]],-2][[1]]},{i,Length[Fl[[2]]]}]/.th[i_]:>i;
Graph[Table[LiArrows[[i,2]]->LiArrows[[i,1]],{i,Length[LiArrows]}],VertexCoordinates->JKVertexCoordinates,VertexLabels->JKVertexLabels,EdgeLabelStyle->Directive[Red,Italic,20],EdgeLabels->Table[(LiArrows[[i,2]]->LiArrows[[i,1]])->LiArrows[[i,3]],{i,Length[LiArrows]}]]];

FlavoredRMatrix[Mat_]:=Module[{RMat=0,l=0},RMat=0Mat;Do[If[Mat[[i,j]]!=0,
RMat[[i,j]]=Table[th[l+k],{k,Abs[Mat[[i,j]]]}];
RMat[[j,i]]=Table[th[l+k],{k,Abs[Mat[[i,j]]]}];
l+=Abs[Mat[[i,j]]];],{i,Length[Mat]},{j,i+1,Length[Mat]}];RMat];

JKIndex[ChargeMatrix_,Nvec_,Etavec_]:=Module[{ListSings,ListStableFlags,Integrand,IndElliptic,ChargeNumMatrix,ListDegrees,j},
If[Length[Etavec]!=Plus@@Nvec,Print["The length of the dimension and stability vectors do not match !"];
];
If[(Length[Transpose[ChargeMatrix]]!=(Plus@@Nvec)+2)&&Length[ChargeMatrix]>0,Print["The width of the charge matrix should equal the rank plus 2 !"];
];
If[Min[Last[Transpose[ChargeMatrix]]]<1,Print["The last column of the charge matrix should be strictly positive integers !"];
];
If[Min[Nvec]<0,Print["The dimension vector should be a vector of positive integers !"];
];
(*JKInitialize[Nvec,JKFrozenCartan]; *)
ChargeNumMatrix=Table[MapAt[#-2&,ChargeMatrix[[i]],Length[Etavec]+1],{i,Length[ChargeMatrix]}];
If[$QuiverNoVM,
  ListSings=FindSingularities[ChargeMatrix],
  ListSings=FindSingularities[CompleteChargeMatrix[ChargeMatrix,Nvec]]
  ];
  JKListAllSings=ListSings;
If[$QuiverVerbose,DisplaySingList[ListSings]];
 ListDegrees=FindDegrees[ListSings,CompleteChargeNumMatrix[ChargeNumMatrix,Nvec]]; 
ListStableFlags=Flatten[Table[FindStableFlags[ListSings[[i,1]],ListSings[[i,2]],Nvec,Etavec]
,{i,Length[ListSings]}],1];
Print[Length[ListStableFlags], " stable flags in total"];
JKListAllStableFlags=ListStableFlags;
(* DisplayFlagList[ListStableFlags]; *)
If[$QuiverVerbose,
  DisplayFlagListDegrees[ListSings,CompleteChargeNumMatrix[ChargeNumMatrix,Nvec],ListStableFlags]
  ]; 
Integrand=ZEuler[ChargeMatrix,Nvec];
PrintTemporary["Evaluating JK residue at flag ",Dynamic[j]];
JKEuler=Table[
JKResidueTrig[ListStableFlags[[j]],Integrand],{j,Length[ListStableFlags]}];
If[$QuiverVerbose,Print["Euler = ",JKEuler," = ",Plus@@Flatten[JKEuler]]];
JKRelevantStableFlags=Select[Table[If[JKEuler[[i]]=!=0,ListStableFlags[[i]],{}],{i,Length[ListStableFlags]}],Length[#]>0&];
Print["From computing the Euler number, ",Length[JKRelevantStableFlags],
 " stable flags appear to contribute"];
If[$QuiverVerbose,DisplayFlagList[JKRelevantStableFlags]];
If[$QuiverTrig==True,
  If[$QuiverMaxPower==0,Integrand=ZTrig[ChargeMatrix,Nvec]
     ,Integrand=Normal[qSeries[ExpandTheta[ZElliptic[ChargeMatrix,Nvec]]]]];
  PrintTemporary["Evaluating JK residue at flag ",Dynamic[j]];
  JKChiGenus=Table[
  JKResidueTrig[JKRelevantStableFlags[[j]],Integrand],{j,Length[JKRelevantStableFlags]}]
  ,If[$QuiverTrig==False,
  Integrand=ZRational[ChargeMatrix,Nvec];
  PrintTemporary["Evaluating JK residue at flag ",Dynamic[j]];
  JKChiGenus=Table[
  JKResidueRational[JKRelevantStableFlags[[j]],Integrand],{j,Length[JKRelevantStableFlags]}];
  ],JKChiGenus=Select[JKEuler,#=!=0&];];
If[$QuiverVerbose,Print["Chi-genus = ",JKChiGenus," =",Plus@@Flatten[JKChiGenus]]];
JKChiGenus
];

JKIndexSplit[ChargeMatrix_,Nvec_,Etavec_,SplitNodes_]:=Module[{ListSings,ListStableFlags,JKListAllIntersections,IndElliptic,ChargeNumMatrix,ListDegrees,Integrand,j,SplitMask},
If[Length[Etavec]!=Plus@@Nvec,Print["The length of the dimension and stability vectors do not match !"];
];
If[(Length[Transpose[ChargeMatrix]]!=(Plus@@Nvec)+2)&&Length[ChargeMatrix]>0,Print["The width of the charge matrix should equal the rank plus 2 !"];
];
If[Min[Last[Transpose[ChargeMatrix]]]<1,Print["The last column of the charge matrix should be strictly positive integers !"];
];
If[Min[Nvec]<0,Print["The dimension vector should be a vector of positive integers !"];
];
ChargeNumMatrix=Table[MapAt[#-2&,ChargeMatrix[[i]],Length[Etavec]+1],{i,Length[ChargeMatrix]}];
SplitMask=Table[If[Length[Position[SplitNodes,i]]>0,1,0],{i,Length[Nvec]}];
(* list of one representative per cycle shape, per node *) 
JKListAllPerms=ListPermutationsWithMultiplicity[SplitMask Nvec];
Print[Length[JKListAllPerms]," partitions with coefficient in table below:"];
Print[MatrixForm[Table[{Map[PermutationToPartition,JKListAllPerms[[k,1]]],JKListAllPerms[[k,2]]},{k,Length[JKListAllPerms]}]]];
JKListAllSings={};
JKListAllStableFlags={};
Do[
If[$QuiverNoVM,
  ListSings=FindSingularities[ChargeMatrix],
  ListSings=FindSingularities[PartialChargeMatrix[ChargeMatrix,Nvec,JKListAllPerms[[k,1]]]]];
ListStableFlags=Flatten[Table[FindStableFlags[ListSings[[i,1]],ListSings[[i,2]],Nvec,Etavec]
,{i,Length[ListSings]}],1];
(* return the list of stable flags for given decomposition of Nvec *)
 JKListAllSings=Append[JKListAllSings,ListSings];
 JKListAllStableFlags=Append[JKListAllStableFlags,ListStableFlags];
Print["Partition",Map[PermutationToPartition,JKListAllPerms[[k,1]]],": ", 
 Length[ListSings]," intersections, ",Length[ListStableFlags], " stable flags in total"];
,{k,Length[JKListAllPerms]}
];
JKListAllIntersections=DeleteDuplicates[Map[First,Flatten[JKListAllSings,1]]];
Print[Length[JKListAllIntersections]," distinct intersections in total"];

JKEuler=Table[
  Print["Partition ",Map[PermutationToPartition,JKListAllPerms[[k,1]]]];
 ListDegrees=FindDegrees[JKListAllSings[[k]],ChargeNumMatrix]; 
 If[$QuiverVerbose, DisplaySingList[JKListAllSings[[k]]];
  (*DisplayFlagList[JKListAllStableFlags[[k]]]; *)
   DisplayFlagListDegrees[JKListAllSings[[k]],ChargeNumMatrix,JKListAllStableFlags[[k]]]
   ]; 
Integrand=ZEulerPartial[ChargeMatrix,Nvec,JKListAllPerms[[k,1]]];
PrintTemporary["Evaluating JK residue at flag (",k,",",Dynamic[j],")"];
JKListAllPerms[[k,2]]Table[
JKResidueTrig[JKListAllStableFlags[[k,j]],Integrand],{j,Length[JKListAllStableFlags[[k]]]}]
  ,{k,Length[JKListAllPerms]}];
If[$QuiverVerbose,Print["Euler = ",JKEuler," = ",Plus@@Flatten[JKEuler]]];

(* identify singularities with non-zero contributions to Euler characteristics *)
JKRelevantStableFlags=Table[Select[Table[If[JKEuler[[k,j]]=!=0,JKListAllStableFlags[[k,j]],{}],{j,Length[JKListAllStableFlags[[k]]]}],Length[#]>0&],{k,Length[JKListAllPerms]}];
Print["From computing the Euler number, ", Map[Length,JKRelevantStableFlags]," stable flags appear to contribute: "];

JKChiGenus=Table[
  Print["Partition ",Map[PermutationToPartition,JKListAllPerms[[k,1]]]];
 (*  ListDegrees=FindDegrees[JKListAllSings[[k]],ChargeNumMatrix]; *)
  If[$QuiverVerbose,DisplayFlagList[JKRelevantStableFlags[[k]]]];
  If[$QuiverTrig==True,
If[$QuiverMaxPower==0,
Integrand=ZTrigPartial[ChargeMatrix,Nvec,JKListAllPerms[[k,1]]],
 Integrand=Normal[qSeries[ExpandTheta[ZEllipticPartial[ChargeMatrix,Nvec,JKListAllPerms[[k,1]]]]]]];
PrintTemporary["Evaluating JK residue at flag (",k,",",Dynamic[j],")"];
JKListAllPerms[[k,2]]Table[
JKResidueTrig[JKRelevantStableFlags[[k,j]],Integrand],{j,Length[JKRelevantStableFlags[[k]]]}]
,If[$QuiverTrig==False,
Integrand=ZRationalPartial[ChargeMatrix,Nvec,JKListAllPerms[[k,1]]];
PrintTemporary["Evaluating JK residue at flag (",k,",",Dynamic[j],")"];
JKListAllPerms[[k,2]]Table[
JKResidueRational[JKRelevantStableFlags[[k,j]],Integrand],{j,Length[JKRelevantStableFlags[[k]]]}]
],Select[JKEuler[[k]],#=!=0&]] ,{k,Length[JKListAllPerms]}];
If[$QuiverVerbose,Print["Chi-genus = ",JKChiGenus," =",Expand[Plus@@Flatten[JKChiGenus]]]];
JKChiGenus
];


(* ::Section:: *)
(*Flow tree formula*)


FlowTreeFormula[Mat_,Cvec_,Nvec_]:=OmAttbToOmAtt[FlowTreeFormulaRat[Mat,Cvec,Nvec]];

FlowTreeFormulaRat[Mat_,Cvec_,Nvec_]:=Module[{RMat,QPoinca,Cvec0},
  If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1,      
  Print["FlowTreeFormula: Length of DSZ matrices, FI and dimension vectors do not match !"]];
  If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["FlowTreeFormulaRat: DSZ matrix is not antisymmetric !"]];
  If[Max[Nvec]<0,Print["FlowTreeFormulaRat: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,       
		Print["FlowTreeFormula: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0]] ;
RMat=Table[Random[Integer,{1,1000}],{i,Length[Mat]},{j,Length[Mat]}];
RMat=1/1000/$QuiverPerturb1 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,Length[Mat]},{j,Length[Mat]}];
  If[$QuiverVerbose,PrintTemporary["FlowTreeFormulaRat: Evaluating tree indices..."]]; 
  QPoinca=EvalTreeIndex[Mat,Mat+RMat,Cvec0,TreePoincarePolynomialRat[Nvec,y]] 
];

TreePoincarePolynomialRat[gam_,y_]:=Module[{JKListAllPart},
	JKListAllPart=ListAllPartitions[gam];
    OmAttb[gam,y]+Sum[Treeg[JKListAllPart[[i]],y]SymmetryFactor[JKListAllPart[[i]]]
		Product[OmAttb[JKListAllPart[[i,j]],y],{j,Length[JKListAllPart[[i]]]}],{i,Length[JKListAllPart]}]];

EvalTreeIndex[Mat_,PMat_,Cvec_,f_]:=f/.{Treeg[Li_,y_]:>
  TreeIndex[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]};
	
TreeF[Mat_,Cvec_]:=Module[{ListPlaneTrees},
  ListPlaneTrees=Groupings[Range[Length[Mat]],2];
  Sum[PlaneTreeSign[Mat,Cvec,ListPlaneTrees[[i]]],{i,Length[ListPlaneTrees]}]
];	

PlaneTreeSign[Mat_,Cvec_,Li_]:=Module[{Li1,Li2,g12,Cvec2},
  (* here Li is a grouping specifying a plane tree *)
  If[Depth[Li]==1,1,
  If[Depth[Li]==2,
    Li1=Flatten[{Li[[1]]}];
    Li2=Flatten[{Li[[2]]}];
    1/2(Sign[DSZProdAbelian[Mat,Li1,Li2]]+Sign[Sum[Cvec[[Li1[[i]]]],{i,Length[Li1]}]]),
  Li1=Flatten[{Li[[1]]}];
  Li2=Flatten[{Li[[2]]}];
g12=DSZProdAbelian[Mat,Li1,Li2];
 If[(g12==0)|| Sign[g12]!=Sign[Sum[Cvec[[Li1[[i]]]],{i,Length[Li1]}]],0,
Cvec2=Cvec+Sum[Cvec[[Li1[[j]]]],{j,Length[Li1]}]/g12
      Table[DSZProdAbelian[Mat,Li1,{i}]+DSZProdAbelian[Mat,Li2,{i}],{i,Length[Mat]}];
 Sign[g12]
   PlaneTreeSign[Mat,Cvec2,Li[[1]]]*PlaneTreeSign[Mat,Cvec2,Li[[2]]]
  ]]]];
	
TreeIndex[Mat_,PMat_,Cvec_,y_]:=Module[{m,ListPerm,i,j,k,RMat,RCvec},
	m=Length[Cvec];
	If[$QuiverVerbose,
		If[Max[Flatten[PMat-Mat]]>1/2,Print["TreeIndex: PMat is not close to Mat !"]];
        If[Abs[Plus@@Cvec]>$QuiverPrecision,Print["TreeIndex: Cvec does not sum to zero !"]];
	];
	ListPerm=Permutations[Range[m]];
        Do[ If[Abs[Sum[Cvec[[ListPerm[[j,i]]]],{i,k}]]<=$QuiverPrecision, 
           If[Abs[Sum[Mat[[ListPerm[[j,i1]],ListPerm[[j,i2]]]],
                {i1,k},{i2,k+1,m}]]>$QuiverPrecision,
               Print["CoulombIndex: FI sit on wall of marginal stability"];Break[]];
          ],{k,1,IntegerPart[m/2]},{j,Length[ListPerm]}
       ];
	(* RMat is a further eps_ 2 perturbation *)
	RMat=Table[Random[Integer,{1,100000}],{i,m},{j,m}];	
	RMat=1/100000/$QuiverPerturb2 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,m},{j,m}];
	RCvec=1/1000/$QuiverPerturb2 Table[Random[Integer,{1,1000}],{i,m}];
	RCvec[[m]]=-Sum[RCvec[[i]],{i,m-1}];
	If[$QuiverVerbose&&m>3,PrintTemporary["TreeIndex: evaluating for ",m," centers"]];
    (y-1/y)^(1-m) (-1)^(Sum[QuiverMultiplierMat[i,j] Mat[[i,j]],{i,Length[Cvec]},{j,i+1,m}]+m-1)
Which[$QuiverFlowTreeOpt==0,
        Sum[y^( Sum[QuiverMultiplierMat[ListPerm[[k,i]],ListPerm[[k,j]]] 
        Mat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,i+1,m}])
		TreeF[Table[PMat[[ListPerm[[k,i]],ListPerm[[k,j]]]]+
					   RMat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,m}],
                 Table[Cvec[[ListPerm[[k,i]]]]+RCvec[[ListPerm[[k,i]]]],{i,m}]],
       {k,Length[ListPerm]}],
       $QuiverFlowTreeOpt==1,
  Sum[y^( Sum[QuiverMultiplierMat[ListPerm[[k,i]],ListPerm[[k,j]]] Mat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,i+1,m}])
		TreeFAlt1[Table[PMat[[ListPerm[[k,i]],ListPerm[[k,j]]]]+
					   RMat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,m}],
                 Table[Cvec[[ListPerm[[k,i]]]]+RCvec[[ListPerm[[k,i]]]],{i,m}]],
       {k,Length[ListPerm]}],
       $QuiverFlowTreeOpt==2,
  Sum[y^( Sum[QuiverMultiplierMat[ListPerm[[k,i]],ListPerm[[k,j]]] Mat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,i+1,m}])
		TreeFAlt2[Table[PMat[[ListPerm[[k,i]],ListPerm[[k,j]]]]+
					   RMat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,m}],
                 Table[Cvec[[ListPerm[[k,i]]]]+RCvec[[ListPerm[[k,i]]]],{i,m}]], 
       {k,Length[ListPerm]}]
       ]
];
	
TreeFAlt1[Mat_,Cvec_]:=Module[{Li,n},
  n=Length[Mat];
  Which[n==1,1,
  n==2,1/2(Sign[Cvec[[1]]]+Sign[Mat[[1,2]]]),
  n>2,
  Li=Select[PlaneTreeSplitList[n],(Length[#]<n)&];
  Plus@@Flatten[{1/2^(n-1)Product[Sign[Sum[Cvec[[k]],{k,i}]],{i,n-1}]
  ,Table[-TreeFAlt1[SubDSZAbelian[Mat,Li[[i]]],SubCvecAbelian[Cvec,Li[[i]]]]
  Product[TreeFAlt1Att[Table[Mat[[Li[[i,j,k]],Li[[i,j,l]]]],{k,Length[Li[[i,j]]]},{l,Length[Li[[i,j]]]}]],{j,Length[Li[[i]]]}],
  {i,Length[Li]}]}]
]];

TreeFAlt1Att[Mat_]:=Module[{Li,n},
n=Length[Mat];
Which[n==1,1,
n>=2,1/2^(n-1)Product[Sign[Sum[Mat[[k,j]],{k,n},{j,i}]],{i,n-1}]]];	
	
TreeFAlt2[Mat_,Cvec_]:=Module[{Li,n},
  n=Length[Mat];
  Which[n==1,1,
  n==2,1/2(Sign[Cvec[[1]]]+Sign[Mat[[1,2]]]),
  n>2,
  Li=Select[PlaneTreeSplitList[n],(Length[#]<n-1)&&(Length[Position[Map[Length,#],2]]==0)&];
  Plus@@Flatten[{1/2^(n-1)Product[Sign[Sum[Cvec[[k]],{k,i}]]+Sign[Mat[[i,i+1]]],{i,n-1}]
  ,Table[-TreeFAlt2[SubDSZAbelian[Mat,Li[[i]]],SubCvecAbelian[Cvec,Li[[i]]]]
  Product[TreeFAlt2Att[Table[Mat[[Li[[i,j,k]],Li[[i,j,l]]]],{k,Length[Li[[i,j]]]},{l,Length[Li[[i,j]]]}]],{j,Length[Li[[i]]]}],
  {i,Length[Li]}]}]
]];

TreeFAlt2Att[Mat_]:=Module[{Li,n},
  n=Length[Mat];
  Which[n==1,1,
  n==2,0,
  n>2,1/2^(n-1)Product[Sign[Sum[Mat[[k,j]],{k,n},{j,i}]]+Sign[Mat[[i,i+1]]],{i,n-1}]]];	
	
PlaneTreeSplitList[n_]:=Module[{i,li},If[n==1,{{{1}}},
  li=PlaneTreeSplitList[n-1];
  Flatten[Table[{Append[Drop[li[[i]],-1],Union[Last[li[[i]]],{n}]],Append[li[[i]],{n}]},{i,Length[li]}],1]
]];

DSZProdAbelian[Mat_,Li1_,Li2_]:=Sum[Mat[[Li1[[i]],Li2[[j]]]],{i,Length[Li1]},{j,Length[Li2]}];

SubDSZAbelian[Mat_,Li_]:=Table[Sum[Mat[[Li[[i,k]],Li[[j,l]]]],{k,Length[Li[[i]]]},{l,Length[Li[[j]]]}],{i,Length[Li]},{j,Length[Li]}];

SubCvecAbelian[Cvec_,Li_]:=Table[Sum[Cvec[[Li[[i,k]]]],{k,Length[Li[[i]]]}],{i,Length[Li]}];

SubFIAbelian[Cvec_,Li_]:=Table[Sum[Cvec[[Li[[i,k]]]],{k,Length[Li[[i]]]}],{i,Length[Li]}];

ListFirstWalls[Mat_,Cvec_,Nvec_]:=Module[{Li,LiDSZ,LiDSZNonZero,LiCvec,LiSimul,LiBatch,PrimBasis},
Li=BinarySplits[Nvec];
(* table of DSZ products <g_L,g_R> *)
LiDSZ=Table[Sum[Li[[k,i]](Nvec[[j]]-Li[[k,j]])Mat[[i,j]],{i,Length[Mat]},{j,Length[Mat]}],{k,Length[Li]}];
LiDSZNonZero=Select[Range[Length[LiDSZ]],LiDSZ[[#]]!=0&];
(* table of FI parameters after discrete flow *)
LiCvec=Table[If[LiDSZ[[k]]!=0,Cvec+Table[Sum[Nvec[[j]]Mat[[j,i]],{j,Length[Nvec]}],{i,Length[Nvec]}]Sum[Li[[k,i]]Cvec[[i]],{i,Length[Nvec]}]/LiDSZ[[k]],{}],{k,Length[Li]}];
(* collect g_L by batches such that all reach the wall at the same time *)
LiSimul=Select[Union[Table[If[LiDSZ[[k]]!=0,Select[LiDSZNonZero,Plus@@(LiCvec[[k]] Li[[#]])==0&],{}],{k,Length[Li]}]],Length[#]>0&];
Table[
LiBatch=Table[{ToPrimitive[Li[[LiSimul[[l,k]]]]],ToPrimitive[Nvec-Li[[LiSimul[[l,k]]]]]},{k,Length[LiSimul[[l]]]}];
MaximalBy[LiBatch,#[[1,2]]+#[[2,2]]&][[1]],{l,Length[LiSimul]}]];

NonAbelianFlowTreeFormula[Mat_,Cvec_,Nvec_]:=Module[{Li,LiWalls,gL,gR,gLR,Nvec2,Cvec2,Cvecflip,ListAllPart},
If[(Length[Select[Nvec,#>0&]]<=1)||Plus@@(Nvec(Cvec^2))==0,
(*Print[Nvec,": no flow"];*)
OmAttb[Nvec,y],
PrintTemporary["NonAbelianFlowTreeFormula: ",Nvec];
LiWalls=ListFirstWalls[Mat,Cvec, Nvec];
Plus@@Prepend[Table[
{gL,gR}={LiWalls[[l,1,1]],LiWalls[[l,2,1]]};
Nvec2={LiWalls[[l,1,2]],LiWalls[[l,2,2]]};
Cvec2={gL. Cvec,gR. Cvec};
gLR=DSZProd[Mat,gL,gR];
Cvecflip=Table[Sum[Nvec[[j]]Mat[[j,i]],{j,Length[Nvec]}],{i,Length[Nvec]}]Sum[gL[[i]]Cvec[[i]],{i,Length[Nvec]}]/gLR;
(*Print[Nvec2,",",gLR,",",Cvecflip]; *)
ListAllPart=Drop[ListAllPartitions[Nvec2],1];
If[gLR Cvec2[[1]]<0,0,
Sum[If[$QuiverFlowTreeMethod,
EvalReinekeIndex[{{0,gLR},{-gLR,0}},Cvec2,Coulombg[ListAllPart[[i]],y]],EvalCoulombIndex[{{0,gLR},{-gLR,0}},{{0,gLR},{-gLR,0}},Cvec2,Coulombg[ListAllPart[[i]],y]]]
SymmetryFactor[ListAllPart[[i]]]
		Product[NonAbelianFlowTreeFormula[Mat,Cvec+Cvecflip/Nvec2[[2]],ListAllPart[[i,j]].{gL,gR}],{j,Length[ListAllPart[[i]]]}],
{i,Length[ListAllPart]}]]
,{l,Length[LiWalls]}],OmAttb[Nvec,y]]
]];




(* ::Section:: *)
(*Attractor tree formula*)


AttractorTreeFormula[Mat_,Cvec_,Nvec_]:=OmAttbToOmAtt[AttractorTreeFormulaRat[Mat,Cvec,Nvec]];

AttractorTreeFormulaRat[Mat_,Cvec_,Nvec_]:=Module[{RMat,QPoinca,Cvec0},
  If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1,      Print["AttractorTreeFormulaRat: Length of DSZ matrices, FI and dimension vectors do not match !"]];
  If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["AttractorTreeFormulaRat: DSZ matrix is not antisymmetric !"]];If[Max[Nvec]<0,Print["AttractorTreeFormulaRat: The dimension vector must be positive !"]];
 If[Max[Nvec]<0,Print["TreeFlowFormula: The dimension vector must be positive !"]];
  If[Plus@@Nvec==0,Return[0]];
  If[Plus@@Nvec==1,Return[1]];
Cvec0=Cvec-(Plus@@(Nvec Cvec))/(Plus@@Nvec);
  If[(Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision)&&$QuiverVerbose,       
		Print["AttractorTreeFormulaRat: FI terms do not sum up to zero, shifting",Cvec," to ",Cvec0]] ;
  If[$QuiverVerbose,PrintTemporary["AttractorTreeFormulaRat: Evaluating tree indices..."]]; 
  QPoinca=EvalAttractorIndex[Mat,Cvec0,TreePoincarePolynomialRat[Nvec,y]] 
];

AttractorIndex[Mat_,Cvec_,y_]:=Module[{m,ListPerm,ListVertices},
m=Length[Mat];
If[$QuiverVerbose&&m>3,PrintTemporary["AttractorIndex: evaluating for ",m," centers"]];
ListPerm=Permutations[Range[m]];
ListVertices=Map[AttractorTreeVertices,AttractorTreeList[m]];
Sum[(-y)^( Sum[QuiverMultiplierMat[ListPerm[[k,i]],ListPerm[[k,j]]] Mat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,i+1,m}])AttractorF[ListVertices,Mat[[ListPerm[[k]],ListPerm[[k]]]],Cvec[[ListPerm[[k]]]]],{k,Length[ListPerm]}]/(y-1/y)^(m-1)];

EvalAttractorIndex[Mat_,Cvec_,f_]:=f/.{Treeg[Li_,y_]:>
 AttractorIndex[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]};

AttractorF[ListVertices_,Mat_,Cvec_]:=Module[{Li,RootVertex,i,k},
Sum[
RootVertex=Last[ListVertices[[k]]];
(-1)^(Length[ListVertices[[k]]]-1)(Attractorg[SubDSZAbelian[Mat,RootVertex],SubFIAbelian[Cvec,RootVertex]]-Attractorg[SubDSZAbelian[Mat,RootVertex]]) 
Product[
Attractorg[SubDSZAbelian[Mat,ListVertices[[k,i]]]],{i,Length[ListVertices[[k]]]-1}],{k,Length[ListVertices]}]
];

Attractorg[Mat_,Cvec_]:=
Module[{Gam,m},Gam=Table[Sum[Cvec[[i]],{i,1,k}],{k,Length[Mat]-1}];
m=Count[Gam,0];If[OddQ[m],0,1/(m+1)
Product[If[Gam[[k]]==0,1,Sign[-Gam[[k]]]],{k,Length[Mat]-1}]/2^(Length[Mat]-1)]];
Attractorg[Mat_]:=Attractorg[Mat,ConstantArray[1,Length[Mat]].Mat];

AttractorTreeList[n_]:=Groupings[Range[n],Drop[Range[n],1]];

(* compute charges attached at each vertex; the last is the root vertex *)
AttractorTreeVertices[t_]:=Module[{Triples,Triple,Li,LiCharges},
Triples=AttractorTreeTriples[t];
LiCharges={};
While[Length[Triples]>0,
Triple=First[Triples];
AppendTo[LiCharges,Drop[Triple,1]];
Triples=Drop[Triples,1]//.{Triple[[1]]:>Flatten[Drop[Triple,1]]};
];
Table[If[IntegerQ[LiCharges[[i,j]]],{LiCharges[[i,j]]},LiCharges[[i,j]]],{i,Length[LiCharges]},{j,Length[LiCharges[[i]]]}]
];

(* generate list of vertices with their descendants - taken from GaltHat *)
AttractorTreeTriples[t_]:=Module[{Li,nM,po,t1},
t1=t;Li={};
While[Length[t1]>0,
nM=Max[t1];
(* look for all lists which do not contain sublists *)
po=Cases[t1,x_List/;VectorQ[x],Infinity];
If[Depth[t1]==2,
AppendTo[Li,Flatten[{nM+1,t1}]];t1={};,
Do[
AppendTo[Li,Flatten[{nM+i,po[[i]]}]];
t1=(t1/.po[[i]]->nM+i);
,{i,Length[po]}]];
];
Li];






(* ::Section:: *)
(*Joyce formula (formerly called Joyce-Song)*)


JoyceSongFormula[Mat_,Cvec1_,Cvec2_,f_]:=JoyceFormula[Mat,Cvec1,Cvec2,f];

JoyceFormula[Mat_,Cvec1_,Cvec2_,f_]:=f/.{
Omb[Nvec_,y_]:>Module[{Li},
Li=ListAllPartitions[Nvec];
Sum[JoyceIndex[Mat,Li[[i]],Cvec1,Cvec2,y]Product[Omb[Li[[i,j]],y],{j,Length[Li[[i]]]}],{i,Length[Li]}]],
HiggsG[Nvec_,y_]:>Module[{Li,Per},
Li=ListAllPartitions[Nvec];
Sum[Per=Permutations[Li[[i]]];
Sum[SFactor[Per[[j]],Cvec1,Cvec2](-1)^(Length[Per[[j]]]-1)/(y-1/y)^(Length[Per[[j]]]-1)Product[HiggsG[Per[[j,k]],y],{k,Length[Per[[j]]]}]
(-y)^(-Sum[DSZProd[Mat,Per[[j,k]],Per[[j,l]]],{k,Length[Per[[j]]]},{l,k+1,Length[Per[[j]]]}]),{j,Length[Per]}],{i,Length[Li]}]]};



SFactor[Li_,Cvec1_,Cvec2_]:=Product[If[Slope[Li[[i]],Cvec1]<=Slope[Li[[i+1]],Cvec1],If[Slope[Sum[Li[[j]],{j,1,i}],Cvec2]>Slope[Sum[Li[[j]],{j,i+1,Length[Li]}],Cvec2],-1,0],If[Slope[Sum[Li[[j]],{j,1,i}],Cvec2]<=Slope[Sum[Li[[j]],{j,i+1,Length[Li]}],Cvec2],1,0]],{i,1,Length[Li]-1}];

UFactor[al_,Cvec1_,Cvec2_]:=Module[{Par1,Par2,Ufactor1,altot,be,ga,Inter},Par1=Flatten[Map[Permutations,IntegerPartitions[Length[al]]],1] ;
altot=Sum[al[[i]],{i,Length[al]}];
Ufactor1=0;
Do[
Inter=PartitionToInvervals[Par1[[p1]]];
be=Table[Sum[al[[i]],{i,Inter[[j]]+1,Inter[[j+1]]}],{j,Length[Par1[[p1]]]}];
If[ (* test if all alphas have same slope *)Union[Flatten[Table[Slope[be[[j]],Cvec1]-Slope[al[[i]],Cvec1],{j,1,Length[Par1[[p1]]]},{i,PartitionToInvervals[Par1[[p1]]][[j]]+1,PartitionToInvervals[Par1[[p1]]][[j+1]]}]]]=={0},
Par2=Flatten[Map[Permutations,IntegerPartitions[Length[Par1[[p1]]]]],1];
Do[
Inter=PartitionToInvervals[Par2[[p2]]];
ga=Table[Sum[be[[i]],{i,Inter[[j]]+1,Inter[[j+1]]}],{j,Length[Par2[[p2]]]}];
(* test if all gammas have same slope *)
If[Union[Flatten[Table[Slope[ga[[j]],Cvec2]-Slope[altot,Cvec2],{j,1,Length[Par2[[p2]]]}]]]=={0},
Ufactor1+=(-1)^(Length[Par2[[p2]]]-1)/Length[Par2[[p2]]] Product[SFactor[Sequence[Table[be[[i]],{i,PartitionToInvervals[Par2[[p2]]][[j]]+1,PartitionToInvervals[Par2[[p2]]][[j+1]]}]],Cvec1,Cvec2],{j,Length[Par2[[p2]]]}]/Product[Par1[[p1,i]]!,{i,Length[Par1[[p1]]]}];
],{p2,1,Length[Par2]}];
],{p1,1,Length[Par1]}];Ufactor1];

LFactor[Mat_,Li_,y_]:=Module[{n,ListPruferCode,ListPairs},
n=Length[Li];
ListPruferCode=If[n>2,Flatten[Outer[List,Sequence@@Table[Range[n],{n-2}]],n-3],{{}}];
ListPairs=Table[EdgeList[CodeToLabeledTreeAlt[ListPruferCode[[k]]]]/.{i_<->j_:>{i,j}},{k,Length[ListPruferCode]}];
Sum[(* sum over trees k *)
Product[(* product over edges i *)
DSZkappa[DSZProd[Mat,Li[[ListPairs[[k,i,1]]]],Li[[ListPairs[[k,i,2]]]]],y]
,{i,Length[ListPairs[[k]]]}],
{k,Length[ListPairs]}]
];

JoyceIndex[Mat_,Li_,Cvec1_,Cvec2_,y_]:=Module[{Per},
Per=Permutations[Li];
If[$QuiverVerbose,PrintTemporary["JoyceIndex: evaluating for ",Length[Li]," centers"]];
Sum[UFactor[Per[[j]],Cvec1,Cvec2]
 (-1)^(Length[Per[[j]]]-1)/(y-1/y)^(Length[Per[[j]]]-1)
 (-y)^(-Sum[ DSZProd[Mat,Per[[j,k]],Per[[j,l]]],{k,Length[Per[[j]]]},
 {l,k+1,Length[Per[[j]]]}]),{j,Length[Per]}]];

JoyceIndexAlt[Mat_,Li_,Cvec1_,Cvec2_,y_]:=Module[{n,Per,ListPruferCode,ListPairs},
n=Length[Li];
ListPruferCode=If[n>2,Flatten[Outer[List,Sequence@@Table[Range[n],{n-2}]],n-3],{{}}];
ListPairs=Table[EdgeList[CodeToLabeledTreeAlt[ListPruferCode[[k]]]]/.{i_<->j_:>{i,j}},{k,Length[ListPruferCode]}];
Per=Permutations[Li];
If[$QuiverVerbose,PrintTemporary["JoyceIndexAlt: evaluating for ",Length[Li]," centers"]];
(-1)^(Sum[DSZProd[Mat,Li[[i]],Li[[j]]],{i,n},{j,i+1,n}])/2^(n-1)
Sum[(* sum over permutations j *)UFactor[Per[[j]],Cvec1,Cvec2]
Sum[(* sum over trees k *)
Product[(* product over edges i *)
DSZkappa[DSZProd[Mat,Per[[j,ListPairs[[k,i,1]]]],Per[[j,ListPairs[[k,i,2]]]]],y]
,{i,Length[ListPairs[[k]]]}],
{k,Length[ListPairs]}]
,{j,Length[Per]}]];

Slope[Nvec_,Cvec_]:=Sum[Nvec[[i]] Cvec[[i]],{i,Length[Nvec]}]/Plus@@Nvec;

(** turn integer partition of length l into intervals a_0<a_1<...<a_l **)
PartitionToInvervals[pa_]:=Table[Sum[pa[[j]],{j,1,i}],{i,0,Length[pa]}];

DSZProd[Mat_,Nvec1_,Nvec2_]:=Sum[QuiverMultilplierMat[i,j] Mat[[i,j]]Nvec1[[i]]Nvec2[[j]],{i,Length[Nvec1]},{j,Length[Nvec2]}];

DSZkappa[m_,y_]:=(y^m-y^(-m))/(y-1/y);

(* Substitute for Combinatorica : *)
CodeToLabeledTreeAlt[l_List]:=Module[{m=Range[Length[l]+2],x,i},TreeGraph[Append[Table[x=Min[Complement[m,Drop[l,i-1]]];m=Complement[m,{x}];
UndirectedEdge@@Sort[{x,l[[i]]}],{i,Length[l]}],UndirectedEdge@@Sort[m]]]]/;Complement[l,Range[Length[l]+2]]=={};

DTSpectrumFromOmAtt[Mat_,Cvec_,Nvec_]:=Module[{n,Nvec0,Cvec0,Ind,Li},
Li={};
Do[Nvec0=Table[n[i],{i,Length[Mat]}];
If[Plus@@Nvec0>0,Cvec0=Cvec-Plus@@(Cvec Nvec0)/Plus@@Nvec0;
Ind=AttractorTreeFormula[Mat,Cvec0,Nvec0]/.y->y$;
AppendTo[Li,Omb[Nvec0,y_]->Ind]],
##]&@@Table[{n[i],0,Nvec[[i]]},{i,Length[Mat]}];Li];

TrivialStackInvariant[Mat_,Cvec_,Nvec_]:=Simplify[HiggsGToOmb[JoyceFormula[Mat,Cvec,0Cvec,HiggsG[Nvec,y]]]/.{Omb[gam_,y_]:>1/;Plus@@gam==1}];

GaugeMotive[Nvec_,y_]:=Product[y^(2Nvec[[i]]^2)Product[1-y^(-2j),{j,Nvec[[i]]}],{i,Length[Nvec]}];


(* ::Section:: *)
(*Non-commutative DT invariants*)


PlethysticExp[f_,Nn_]:=Exp[Sum[(f/.{x[i_]:>x[i]^k,y->y^k})/k,{k,1,Nn}]];

PlethysticLog[f_,Nn_]:=Sum[MoebiusMu[k](Log[f]/.{x[i_]:>x[i]^k,y->y^k})/k,{k,1,Nn}];

FramedDSZ[Mat_,Framing_]:=ArrayFlatten[{{{{0}},{Framing}},{-Transpose[{Framing}],Mat}}];

HiggsedDSZ[Mat_,i_,j_]:=Module[{Mat1},Mat1=Table[Mat[[k,l]]+If[k==i&&k!=l,Mat[[j,l]],If[l==i&&k!=l,Mat[[k,j]],0]],{k,Length[Mat]},{l,Length[Mat]}];
Drop[Mat1,{j},{j}]];

ConnectedQuiverQ[Mat_,Nvec_]:=Module[{Nvec0,Mat1},
Nvec0=Map[#!=0&,Nvec];
Mat1=Abs[Transpose[Pick[Transpose[Pick[Mat,Nvec0]],Nvec0]]];
ConnectedGraphQ[AdjacencyGraph[Mat1+Transpose[Mat1]]]
];

FramedFI[Nvec_]:=Module[{Cvec0,Nvec0},
Nvec0=Flatten[{1,Nvec}];Cvec0=Flatten[{$QuiverPerturb1,Table[RandomInteger[{-$QuiverPerturb1,$QuiverPerturb1}]/$QuiverPerturb1,{i,Length[Nvec]}]}];
Cvec0-(Plus@@(Cvec0 Nvec0)/Plus@@Nvec0)ConstantArray[1,Length[Nvec0]]];

EulerNorm[hMat_,Nvec_]:=Sum[Nvec[[i]]^2,{i,Length[hMat]}]-Sum[Length[hMat[[i,j]]]Nvec[[i]]Nvec[[j]],{i,Length[hMat]},{j,Length[hMat]}];

NCDTSeriesFromCrystal[hMat_,Framing_,Nn_]:=Module[{A,A1,Z,CrysLi,Nvec},
Z=1;CrysLi={{}};
Do[A=GrowCrystalList[hMat,Framing,CrysLi];
Z+=Sum[Nvec=CrystalDim[Length[hMat],A[[i]]];
y^(Sum[Framing[[k]] Nvec[[k]],{k,Length[hMat]}]-EulerNorm[hMat,Nvec])
Product[x[k]^Nvec[[k]],{k,Length[hMat]}],{i,Length[A]}];
CrysLi=A; PrintTemporary[l,":",Length[CrysLi]];
A1=Simplify[Table[A[[j,k,2]],{j,Length[A]},{k,Length[A[[j]]]}]/.h3->0];
Print[Tally[Table[Transpose[Tally[A1[[j]]]][[2]],{j,Length[A1]}]]]
,{l,Nn}];
If[$QuiverDisplayCrystal,{Z,A},Z]];

NCDTSeriesFromOmS[Mat_,Framing_,Nmin_,Nmax_]:=Module[{n,Cvec,Cvec0,Ind,Mat1,Nvec,Dim},
Mat1=FramedDSZ[Mat,Framing];Dim=1;
Sum[Nvec=Flatten[{Dim,Table[n[i],{i,Length[Mat]}]}];
If[(Plus@@Nvec<=Nmax+Dim)&&(Plus@@Nvec>=Nmin+1)&&ConnectedQuiverQ[Mat1,Nvec],
PrintTemporary[Nvec];
Cvec0=Flatten[{$QuiverPerturb1,Table[RandomInteger[{-$QuiverPerturb1,$QuiverPerturb1}]/$QuiverPerturb1,{i,Length[Mat]}]}];
Cvec=Cvec0-Plus@@(Cvec0 Nvec)/Plus@@Nvec;
Ind=CoulombBranchFormula[Mat1,Cvec,Nvec];
Simplify[Ind]Product[x[i]^n[i],{i,Length[Mat]}],0],
##]&@@ ({n[#],0,Nmax}&/@Range[Length[Mat]])];
              
NCDTSeriesFromOmAtt[Mat_,Framing_,Nmin_,Nmax_]:=Module[{n,Cvec,Cvec0,Ind,Mat1,Nvec,Dim},
Mat1=FramedDSZ[Mat,Framing];Dim=1;
Sum[Nvec=Flatten[{Dim,Table[n[i],{i,Length[Mat]}]}];
If[(Plus@@Nvec<=Nmax+Dim)&&(Plus@@Nvec>=Nmin)+1&&ConnectedQuiverQ[Mat1,Nvec],
PrintTemporary[Nvec];
Cvec0=Flatten[{$QuiverPerturb1,Table[RandomInteger[{-$QuiverPerturb1,$QuiverPerturb1}]/$QuiverPerturb1,{i,Length[Mat]}]}];
Cvec=Cvec0-Plus@@(Cvec0 Nvec)/Plus@@Nvec;
Ind=FlowTreeFormula[Mat1,Cvec,Nvec];
Simplify[Ind]Product[x[i]^n[i],{i,Length[Mat]}],0],
##]&@@ ({n[#],0,Nmax}&/@Range[Length[Mat]])];

(* from list of Crystals with n atomes, construct list of Crystals with n+1 atomes *)
BondFactor[hMat_,i_,j_,z_]:=Product[z+hMat[[j,i,k]],{k,Length[hMat[[j,i]]]}]/Product[z-hMat[[i,j,k]],{k,Length[hMat[[i,j]]]}];

ChargeFunction[hMat_,Framing_,Crys_,i_,z_]:=VacuumChargeFunction[Framing,i,z]Product[BondFactor[hMat,Crys[[k,1]],i,z-Crys[[k,2]]],{k,Length[Crys]}];
(* standard vacuum charge function *)

VacuumChargeFunction[Framing_,i_,z_]:=(1+Framing[[i]]/z);
(* List allowed atomes to be added *)

AddToCrystal[hMat_,Framing_,i_,Crys_]:=Module[{Psi,FList,RootList,ResidueList},
Psi=Factor[ChargeFunction[hMat,Framing,Crys,i,z]];
FList=Drop[FactorList[Denominator[Psi]],1];
RootList=Table[{i,z}/.Solve[FList[[j,1]]==0,z][[1]],{j,1,Length[FList]}];
ResidueList=Table[!(Residue[Simplify[Psi/.h3->0],{z,(RootList[[j,2]]/.h3->0)}]===0),{j,Length[FList]}]/.h3->0;
Complement[Pick[RootList,ResidueList],Crys]
];

(* List all crystals obtained by adding one atom of any color to crystals in list CrysList *)
GrowCrystalList[hMat_,Framing_,CrysList_]:=Module[{Li,CrysList2,k},
CrysList2={};
Do[PrintTemporary["Adding atoms of type ",i];
Monitor[Do[(*PrintTemporary["Acting on crystal ",k];*)
Li=AddToCrystal[hMat,Framing,i,CrysList[[k]]];
Do[AppendTo[CrysList2,Union[Append[CrysList[[k]],Li[[l]]]]],{l,Length[Li]}];
,{k,Length[CrysList]}],k];
,{i,Length[hMat]}];
DeleteDuplicates[CrysList2]];
CrystalDim[r_,Crys_]:=Module[{Li},Li=Table[Crys[[j,1]],{j,Length[Crys]}];Table[Count[Li,i],{i,r}]];

PlotTiling[hMat_,Nn_,v_,Rang_,Shor_,Perf_:{}]:=Module[{ArrowList,ArrowList2,Labels,v1,v2},
(* produces a list of (color of endpoint, starting point, endpoint, iterating N times excluding arrows in Perf *)
If[Length[v]==2,{v1,v2}=v,{v1,v2}={{-1/2,Sqrt[3]/2},{1,0}}];
(* Print[v1,v2]; 
{v1,v2}={{-1/2,Sqrt[3]/2},{1,0}}; *)
ArrowList={{1,0,0}};
Labels=If[Length[$QuiverVertexLabels]==Length[hMat],$QuiverVertexLabels,Range[Length[hMat]]];
Do[ArrowList2=ArrowList;
Do[
If[Length[hMat[[ArrowList[[k,1]],j]]]>0,
Do[If[Count[Perf,{ArrowList[[k,1]],j,l}]==0,
AppendTo[ArrowList2,{j,ArrowList[[k,3]],ArrowList[[k,3]]+hMat[[ArrowList[[k,1]],j,l]]}]],
{l,Length[hMat[[ArrowList[[k,1]],j]]]}]],{j,Length[hMat]},{k,Length[ArrowList]}]/.{h3->0};
ArrowList=DeleteDuplicates[ArrowList2],{m,Nn}];
Graphics[Table[{Hue[ArrowList[[k,1]]/Length[hMat]],
Arrow[{v1 D[ArrowList[[k,2]],h1]+v2 D[ArrowList[[k,2]],h2],v1 D[ArrowList[[k,3]],h1]+v2 D[ArrowList[[k,3]],h2]},{Shor,Shor}],
Text[Style[Framed[Labels[[ArrowList[[k,1]]]],RoundingRadius->10],Black,Medium],v1 D[ArrowList[[k,3]],h1]+v2 D[ArrowList[[k,3]],h2]]},{k,Length[ArrowList]}],PlotRange->Rang,Frame->True,FrameTicks->None]
];

PlotTiling3D[hMat_,Nn_,v_,Rang_,Perf_:{}]:=Module[{ArrowList,ArrowList2,Labels,v1,v2,v3},
(* produces a list of (color of endpoint, starting point, endpoint, iterating N times excluding arrows in Perf *)
If[Length[v]==3,{v1,v2,v3}=v,{v1,v2,v3}={{1,0,0},{1,0,0},{1,0,0}}];
ArrowList={{1,0,0}};
Labels=If[Length[$QuiverVertexLabels]==Length[hMat],$QuiverVertexLabels,Range[Length[hMat]]];
Do[ArrowList2=ArrowList;
Do[
If[Length[hMat[[ArrowList[[k,1]],j]]]>0,
Do[If[Count[Perf,{ArrowList[[k,1]],j,l}]==0,
AppendTo[ArrowList2,{j,ArrowList[[k,3]],ArrowList[[k,3]]+hMat[[ArrowList[[k,1]],j,l]]}]],
{l,Length[hMat[[ArrowList[[k,1]],j]]]}]],{j,Length[hMat]},{k,Length[ArrowList]}];
ArrowList=DeleteDuplicates[ArrowList2],{m,Nn}];
Graphics3D[
Table[{Hue[ArrowList[[k,1]]/4],Arrow[{v1 D[ArrowList[[k,2]],h1]+v2 D[ArrowList[[k,2]],h2]+v3 D[ArrowList[[k,2]],h3],v1 D[ArrowList[[k,3]],h1]+v2 D[ArrowList[[k,3]],h2]+v3 D[ArrowList[[k,3]],h3]}],Text[Style[Labels[[ArrowList[[k,1]]]],Black,Medium],v1 D[ArrowList[[k,3]],h1]+v2 D[ArrowList[[k,3]],h2]+v3 D[ArrowList[[k,3]],h3]]},{k,Length[ArrowList]}],PlotRange->Rang]
];

PlotToricFan[Fan_]:=Module[{mx1,mx2,my1,my2},
mx1=Min[First[Transpose[Fan]]];mx2=Max[First[Transpose[Fan]]];my1=Min[Last[Transpose[Fan]]];my2=Max[Last[Transpose[Fan]]];Graphics[{Thick,Line[Append[Fan,First[Fan]]]},PlotRange->{{mx1-1/3,mx2+1/3},{my1-1/3,my2+1/3}},GridLines->{Range[mx1,mx2],Range[my1,my2]},Frame->True,FrameTicks->None]];

ListPerfectMatchings[Wp_,Wm_]:=Module[{WL,m,LiPhi,LiCuts},
WL=Union[List@@Wp,List@@Wm];
m=Length[WL];
If[OddQ[m],Print["The number of terms in the potentials do not match !"]];
LiPhi=Union[Flatten[Table[List@@WL[[i]],{i,m}]]];
LiCuts=Subsets[LiPhi,{m/2}];
Select[LiCuts,(WL/.Table[#[[k]]->0,{k,Length[#]}])===ConstantArray[0,m]&]/.Phi[i_,j_,k_]:>{i,j,k}];

HeightMatrixFromPotential[Wp_,Wm_,ijk1_,ijk2_]:=Module[{WL,Li,Mat,EqW,EqV,so,i1,j1,k1,i2,j2,k2},
If[Length[ijk1]==3,{i1,j1,k1}=ijk1,{i1,j1,k1}={1,2,1}];
If[Length[ijk2]==3,{i2,j2,k2}=ijk2,{i2,j2,k2}={1,3,1}];
WL=List@@Expand[Wp+Wm];
Li=Union[Flatten[Table[List@@WL[[i]],{i,Length[WL]}]]]/.Phi[x__]:>{x};
Mat=Table[Count[Li,{i,j,k_}],{i,Max[Li]},{j,Max[Li]}];
EqW=Table[Plus@@List@@WL[[i]]==h3,{i,Length[WL]}];
(* vertex constraint *)
EqV=Table[Sum[Sum[Phi[i,j,k],{k,Mat[[i,j]]}]-Sum[Phi[j,i,k],{k,Mat[[j,i]]}],{j,Length[Mat]}]==0,{i,Length[Mat]}];
so=Solve[Flatten[{EqW,EqV,Phi[i1,j1,k1]==h1,Phi[i2,j2,k2]==h2}]][[1]];
Table[Table[Phi[i,j,k],{k,Mat[[i,j]]}],{i,Length[Mat]},{j,Length[Mat]}]/.so]




(* ::Section:: *)
(*Misc. Utilities*)


(* utilities *)

SymmetryFactor[pa_]:=Length[Permutations[pa]]/Length[pa]!;

OmTRat[gam_,y_]:=DivisorSum[GCD@@gam,(y-1/y)/#/(y^#-1/y^#)OmT[gam/#,y^#]&];

SimplifyOmSbasis[f_]:=f/.{OmS[gam_,y__]:> If[Length[$QuiverOmSbasis]==0,
     If[$QuiverOmSbasis==0,OmS[gam,y],$QuiverOmSbasis],
     $QuiverOmSbasis[[Tr[Position[gam,1]]]]]/; (Plus@@gam==1)};

SimplifyOmSmultbasis[f_]:=f/.{OmS[gam_,y_]:>0/; (Plus@@gam>1)&& 
          (Union[gam]=={0,Plus@@gam}) && ($QuiverOmSbasis!=0)};
          
SimplifyOmAttbasis[f_]:=f/.{OmAtt[gam_,y_]:>1/;Plus@@gam==1,OmAtt[gam_,y_]:>0/; Count[gam,0]==Length[gam]-1};
          
SwapFugacity[f_]:=f /. {OmS[gam_,y^n_]->OmS[gam,y^n,t^n],OmS[gam_,y]->OmS[gam,y,t]};

DropFugacity[f_]:=f /. {OmS[gam_,y_,t_]->OmS[gam,t]};

TestNoLoop[Mat_,Li_]:=Module[{m,MatProd,ListPerm},
	m=Length[Li];
    Which[
	  $QuiverOmSbasis==0,False,
      m==1,False,
      m==2,True,
      $QuiverNoLoop,True,
      !$QuiverTestLoop,False,
      $QuiverTestLoop,
	    MatProd=Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],{i,m},{j,m}];
	    ListPerm=Permutations[Range[m]];
	    Or@@Table[And@@Flatten[Table[MatProd[[ListPerm[[i,j]],ListPerm[[i,k]]]]>=0,{j,m},{k,j+1,m}]],{i,Length[ListPerm]}]
	]
];

TestNoFullLoop[Mat_,Li_]:=Module[{m,MatProd,ListSubsets,ListComplements},
	m=Length[Li];
    Which[
      $QuiverOmSbasis==0,False,
      m==1,False,
      m==2,True,
      $QuiverNoLoop,True,
      !$QuiverTestLoop,False,
      $QuiverTestLoop,
	    MatProd=Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],{i,m},{j,m}];
	    ListSubsets=Subsets[Range[m],{1,m-1}];
        ListComplements=Map[Complement[Range[m],#]&,ListSubsets];
	    Or@@Table[And@@Flatten[
                  Table[MatProd[[ListSubsets[[i,j]],ListComplements[[i,k]]]]>0,
                    {j,Length[ListSubsets[[i]]]},{k,Length[ListComplements[[i]]]}]]
                ,{i,Length[ListSubsets]}]
	]
];

CoulombHNoLoopToZero[Mat_,f_]:= f/.{CoulombH[Li_,gam_,y_]:>0/;TestNoLoop[Mat,Li]};

OmSNoLoopToZero[Mat_,f_]:= f /.{
      OmS[gam_,y_]:>0 /;TestNoLoop[Mat,
         Select[Table[If[j==i,gam[[j]],0],{j,Length[gam]},{i,Length[gam]}],#!=Table[0,{i,Length[Mat]}]&]]};

OmAttNoLoopToZero[Mat_,f_]:= f /.{
      OmAtt[gam_,y_]:>0 /;TestNoLoop[Mat,
         Select[Table[If[j==i,gam[[j]],0],{j,Length[gam]},{i,Length[gam]}],#!=Table[0,{i,Length[Mat]}]&]]};

OmTNoLoopToZero[Mat_,f_]:= f /.{
     OmT[gam_,y_]:>0 /;TestNoLoop[Mat,
         Select[Table[If[j==i,gam[[j]],0],{j,Length[gam]},{i,Length[gam]}],#!=Table[0,{i,Length[Mat]}]&]]};

	
EvalCoulombH3[Mat_,f_]:=f/.{CoulombH[Li_,gam_,y_]:>If[(Length[Li]==3)&&gam=={1,1,1},Module[{Mat3},
	Mat3=Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}];
	If[((Mat3[[1,2]]>0)&&(Mat3[[2,3]]>0)&&(Mat3[[3,1]]>0)
		&&(Mat3[[1,2]]<=Mat3[[2,3]]+Mat3[[3,1]])
	    &&(Mat3[[2,3]]<=Mat3[[1,2]]+Mat3[[3,1]]) 
        &&(Mat3[[3,1]]<=Mat3[[1,2]]+Mat3[[2,3]]))||
	  ((Mat3[[1,2]]<0)&&(Mat3[[2,3]]<0)&&(Mat3[[3,1]]<0)
		&&(-Mat3[[1,2]]<=-Mat3[[2,3]]-Mat3[[3,1]])
	    &&(-Mat3[[2,3]]<=-Mat3[[1,2]]-Mat3[[3,1]]) 
        &&(-Mat3[[3,1]]<=-Mat3[[1,2]]-Mat3[[2,3]])),
	-2/(y-1/y)^2(1+(-1)^($QuiverMultiplier (Mat3[[1,2]]+Mat3[[2,3]]+Mat3[[3,1]])))/2 
	+(y+1/y)/(y-1/y)^2(1-(-1)^($QuiverMultiplier (Mat3[[1,2]]+Mat3[[2,3]]+Mat3[[3,1]])))/2,0]],CoulombH[Li,gam,y]]};

(* SubDSZ[Mat_,Li_]:=
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}]; *)
      
SubDSZ[Mat_,PMat_,Cvec_,Li_]:=
{Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
      Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[PMat]},{l,Length[PMat]}],
      {i,Length[Li]},{j,Length[Li]}],
      Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Cvec]}],{i,Length[Li]}]
};      

OmToOmb[f_]:=f/. {Om[gam_,y_]:>DivisorSum[GCD@@gam,(y-1/y)/(y^#-1/y^#)/# MoebiusMu[#] Omb[gam/#,y^#]&]};

OmbToOm[f_]:=f/. {Omb[gam_,y_]:>DivisorSum[GCD@@gam,(y-1/y)/(y^#-1/y^#)/# Om[gam/#,y^#]&]};

OmAttToOmAttb[f_]:=f/. {OmAtt[gam_,y_]:>DivisorSum[GCD@@gam,(y-1/y)/(y^#-1/y^#)/# MoebiusMu[#] OmAttb[gam/#,y^#]&]};

OmAttbToOmAtt[f_]:=f/. {OmAttb[gam_,y_]:>DivisorSum[GCD@@gam,(y-1/y)/(y^#-1/y^#)/# OmAtt[gam/#,y^#]&]};

ListSubQuivers[Nvec_]:=Module[{k},Flatten[Table[k/@Range[Length[Nvec]],##]&@@({k[#],0,Nvec[[#]]}&/@Range[Length[Nvec]]),
	Length[Nvec]-1]];

(*ListAllPartitions[gam_]:=Module[{m,unit,Li},
	If[Plus@@gam==1, {{gam}},
		m=Max[Select[Range[Length[gam]],gam[[#]]>0&]];
        unit=Table[If[i==m,1,0],{i,Length[gam]}];        
	    Li=ListAllPartitions[gam-unit];
        Union[Map[Sort,
        Union[Flatten[
				Table[Union[Flatten[{{Flatten[{Li[[i]],{unit}},1]},
					    Table[
						  Table[If[j==k,Li[[i,j]]+unit,Li[[i,j]]]
						  ,{j,Length[Li[[i]]]}]
	                    ,{k,Length[Li[[i]]]}]}
                      ,1]]
				,{i,Length[Li]}],1]]
         ,1]]
	]
]*)

ListAllPartitions[gam_]:=Module[{m,unit,Li},
If[$QuiverOnlyMultipleBasisVector,
	 Select[If[Plus@@gam==1, {{gam}},
		m=Max[Select[Range[Length[gam]],gam[[#]]>0&]];
        unit=Table[If[i==m,1,0],{i,Length[gam]}];        
	    Li=ListAllPartitions[gam-unit];
       Union[Map[Sort,
        Union[Flatten[
				Table[Union[Flatten[{{Flatten[{Li[[i]],{unit}},1]},
					    Table[
						  Table[If[j==k,Li[[i,j]]+unit,Li[[i,j]]]
						  ,{j,Length[Li[[i]]]}]
	                    ,{k,Length[Li[[i]]]}]}
                      ,1]],{i,Length[Li]}],1]],1]]
	],TestMultipleBasisVector],
If[Plus@@gam==1, {{gam}},
		m=Max[Select[Range[Length[gam]],gam[[#]]>0&]];
        unit=Table[If[i==m,1,0],{i,Length[gam]}];        
	    Li=ListAllPartitions[gam-unit];
        Union[Map[Sort,
        Union[Flatten[
				Table[Union[Flatten[{{Flatten[{Li[[i]],{unit}},1]},
					    Table[
						  Table[If[j==k,Li[[i,j]]+unit,Li[[i,j]]]
						  ,{j,Length[Li[[i]]]}]
	                    ,{k,Length[Li[[i]]]}]}
                      ,1]]
				,{i,Length[Li]}],1]]
         ,1]]
	]
]];

ListAllPartitionsMult[gam_]:=Module[{Li},
  Li=ListAllPartitions[gam];
  Flatten[Table[ExpandPartitionMult[Tally[Li[[i]]]],{i,Length[Li]}],1]
];

ExpandPartitionMult[LiTally_]:=Module[{Nvec,Ntot,ListMult,ListDrop,ListExp},
  Nvec=First[LiTally][[1]];
  Ntot=LiTally[[1,2]];
  ListMult=Map[Flatten,ListAllPartitions[{Ntot}]]; 
  ListExp=Map[{Nvec,#}&,ListMult,{2}];   
  If[Length[LiTally]==1,ListExp,
    ListDrop=ExpandPartitionMult[Drop[LiTally,1]];
    Flatten[Table[Flatten[{ListExp[[i]],ListDrop[[j]]},1],{i,Length[ListExp]},{j,Length[ListDrop]}],1]
 ]
];

OmTToOmS[f_]:=f/.{OmT[gam_,y_]:>Module[{Li},
  Li=ListAllPartitionsMult[gam];
  OmS[gam,y]+Sum[If[Length[Li[[j]]]>2,
     CoulombH[Table[Li[[j,i,1]],{i,Length[Li[[j]]]}],Table[Li[[j,i,2]],{i,Length[Li[[j]]]}],y]
     Product[OmS[Li[[j,i,1]],y^Li[[j,i,2]]],{i,Length[Li[[j]]]}]
     ,0]
,{j,Length[Li]}]]
};

RandomFI[gam_]:=Module[{m,mnonzero,k,Cvec},
	m=Length[gam];
	mnonzero=Select[Range[m],gam[[#]]>0&];
      If[Length[mnonzero]==0,Cvec=0 Range[m],
        k=Last[mnonzero];
        Cvec=Table[Random[Integer,{-1000,1000}],{i,m}];
        Cvec[[k]]=-Sum[If[i==k,0,gam[[i]]Cvec[[i]]],{i,m}]/gam[[k]];
	];
	Cvec/$QuiverPerturb1
];

RandomCvec[gam_]:=RandomFI[gam];

CyclicQuiverOmS[avec_,t_]:=Module[{n,P,eps,Pexp,x},n=Length[avec]; P=-1/2(t-1/t)/(1/t Product[(1+x[i] t),{i,n}]-t Product[(1+x[i] /t),{i,n}])(t Product[x[i]/(1+x[i] t),{i,n}]+1/t Product[x[i]/(1+x[i]/ t),{i,n}])+ 1/2Sum[(1-x[k]^2)/(1+x[k] t)/(1+x[k]/t)Product[If[i==k,1,x[i]/(1-x[i]/x[k])/(1-x[i]x[k])],{i,n}],{k,n}];
  Pexp=SeriesCoefficient[Series[P/.x[i_]->eps x[i],{eps,0,Plus@@avec}],Plus@@avec];
PrintTemporary["Simplifying"];
Pexp=Simplify[Pexp];
 Do[PrintTemporary["Taking derivative ",i];Pexp=D[Pexp,{x[i],avec[[i]]}]/avec[[i]]!/.x[i]->0,{i,n}];Simplify[Pexp]];

CyclicQuiverDSZ[Li_]:=Map[RotateRight,DiagonalMatrix[Li]]-Transpose[Map[RotateRight,DiagonalMatrix[Li]]];

HirzebruchR[J_,v_]:=1/((1-v)/(1-Exp[-(1-v)J])+v);

GrassmannianPoincare[k_,n_,y_]:=If[k<=n && n>=0,(-y)^(-k(n-k)) QFact[n,y]/QFact[k,y]/QFact[n-k,y],0];

AttractorFI[Mat_,Nvec_]:=-Table[Sum[Mat[[i,j]]Nvec[[j]],{j,Length[Mat]}],{i,Length[Mat]}];

FIFromZ[Nvec_,Zvec_]:=Module[{phi,Cvec},phi=Arg[Plus@@(Nvec Zvec)];
Cvec=Map[Rationalize[#,1/$QuiverPerturb1]&,Im[Exp[-I phi] Zvec]];
 Cvec -(Plus@@(Nvec Cvec))/(Plus@@Nvec)];

QuiverPlot[Mat_]:=GraphPlot[Table[Max[Mat[[i,j]],0],{i,Length[Mat]},{j,Length[Mat]}],
      DirectedEdges->True,MultiedgeStyle->True,VertexLabeling->True];

(* PlotQuiver[hMat_]:=
If[Depth[hMat]>2,GraphPlot[Flatten[Table[ConstantArray[i\[Rule]j,Length[hMat[[i,j]]]],{i,Length[hMat]},{j,Length[hMat]}]],DirectedEdges->True,MultiedgeStyle->True,VertexLabeling->True],GraphPlot[Table[Max[hMat[[i,j]],0],{i,Length[hMat]},{j,Length[hMat]}],
      DirectedEdges->True,MultiedgeStyle->True,VertexLabeling->True]]; *)
     
PlotQuiver[hMat_]:=Module[{Gr,V},
If[Depth[hMat[[1,1]]]>1,Gr=Flatten[Table[ConstantArray[i->j,Length[hMat[[i,j]]]],{i,Length[hMat]},{j,Length[hMat]}]],
Gr=Flatten[Table[ConstantArray[i->j,Max[hMat[[i,j]],0]],{i,Length[hMat]},{j,Length[hMat]}]]];
V=If[Length[$QuiverVertexLabels]==Length[hMat],$QuiverVertexLabels,Range[Length[hMat]]];
Graph[Gr,DirectedEdges->True,VertexLabels->Table[i->V[[i]],{i,Length[hMat]}]]];       
      
(* list loops and associated R-charges *)
ListLoopRCharges[Mat_,RMat_]:=Module[{perm},
perm=FindCycle[AdjacencyGraph[Table[If[Mat[[i,j]]>0,1,0],{i,Length[Mat]},{j,Length[Mat]}]],Infinity,All];
Table[{Table[perm[[i,j,1]],{j,Length[perm[[i]]]}],Plus@@Table[RMat[[perm[[i,j,1]],perm[[i,j,2]]]],{j,Length[perm[[i]]]}]},{i,Length[perm]}]
];

ExpandTheta[f_]:=(f/.Theta[x_]:>-I q^(1/8)(Exp[I Pi x]-Exp[-I Pi x])Product[(1-q^k)(1- q^k Exp[2Pi I x])(1-q^k Exp[-2Pi I x]),{k,1,$QuiverMaxPower}]/.Eta->q^(1/24)Product[1-q^k,{k,1,$QuiverMaxPower}]);

qSeries[f_]:=Series[f,{q,0,$QuiverMaxPower}];

UnitStepWarn[x_]:=Which[x>0,1,x<0,0,x==0,Print["UnitStepWarn: argument vanishes, returns 1/2"];1/2]; 

RandomDSZWithNoLoop[n_,$QuiverMaxPower_]:=Module[{Li,Mat},
Li={{1}};
While[Length[Li]>0,
Mat=Table[Random[Integer,{-$QuiverMaxPower,$QuiverMaxPower}],{i,n},{j,n}];
Mat=Mat-Transpose[Mat];
Li=ListLoopRCharges[Mat,0Mat];
];
Mat];
RandomDSZWithLoop[n_,$QuiverMaxPower_]:=Module[{Li,Mat},
Li={};
While[Length[Li]==0,
Mat=Table[Random[Integer,{-$QuiverMaxPower,$QuiverMaxPower}],{i,n},{j,n}];
Mat=Mat-Transpose[Mat];
Li=ListLoopRCharges[Mat,0Mat];
];
Mat];

TestMultipleBasisVector[Li_]:=And@@Map[Length[Cases[#,Except[0]]]==1&,Li,1];

DSZProd[Mat_,Nvec1_,Nvec2_]:=Sum[Mat[[i,j]]Nvec1[[i]]Nvec2[[j]],{i,Length[Nvec1]},{j,Length[Nvec2]}];

ResidueFast[f_,{x_,x0_}]:=SeriesCoefficient[Series[f,{x,x0,-1}],-1]/.SeriesCoefficient[0,-1]->0;

BinarySplits[Nvec_]:=Module[{Li,Li1,Nl},
If[Plus@@Nvec==1,Li1=Nvec,
Li=Drop[Drop[Flatten[Table[Table[Nl[i],{i,Length[Nvec]}],Evaluate[Sequence@@Table[{Nl[i],0,Nvec[[i]]},{i,Length[Nvec]}]]],Length[Nvec]-1],1],-1];
Li1=Take[Li,Ceiling[Length[Li]/2]];
Li1]];

ToPrimitive[Nvec_]:={Nvec/GCD@@Nvec,GCD@@Nvec};

ReduceDSZMatrix[Mat_,Li_]:=Module[{Mat2=Mat},
Do[
If[Li[[i,1]]==Li[[i,2]],
Do[Mat2[[Li[[i,1]],j]]:=0;
Mat2[[j,Li[[i,1]]]]:=0,{j,Length[Mat]}]
,Mat2[[Li[[i,1]],Li[[i,2]]]]:=0;
Mat2[[Li[[i,2]],Li[[i,1]]]]:=0;],{i,Length[Li]}];Mat2];

HeightMatrixToDSZ[hMat_]:=Table[Length[hMat[[i,j]]]-Length[hMat[[j,i]]],{i,Length[hMat]},{j,Length[hMat]}];

HeightMatrixFromPotential[Wp_,Wm_,ijk1_,ijk2_]:=Module[{WL,Li,Mat,EqW,EqV,so,i1,j1,k1,i2,j2,k2},
If[Length[ijk1]==3,{i1,j1,k1}=ijk1,{i1,j1,k1}={1,2,1}];
If[Length[ijk2]==3,{i2,j2,k2}=ijk2,{i2,j2,k2}={1,3,1}];
WL=List@@Expand[Wp+Wm];
Li=Union[Flatten[Table[List@@WL[[i]],{i,Length[WL]}]]]/.Phi[x__]:>{x};
Mat=Table[Count[Li,{i,j,k_}],{i,Max[Li]},{j,Max[Li]}];
EqW=Table[Plus@@List@@WL[[i]]==h3,{i,Length[WL]}];
(* vertex constraint *)
EqV=Table[Sum[Sum[Phi[i,j,k],{k,Mat[[i,j]]}]-Sum[Phi[j,i,k],{k,Mat[[j,i]]}],{j,Length[Mat]}]==0,{i,Length[Mat]}];
so=Solve[Flatten[{EqW,EqV,Phi[i1,j1,k1]==h1,Phi[i2,j2,k2]==h2}]][[1]];
Table[Table[Phi[i,j,k],{k,Mat[[i,j]]}],{i,Length[Mat]},{j,Length[Mat]}]/.so]

QuiverMultiplierMat[i_,j_]:=If[Depth[$QuiverMultiplier]==1,$QuiverMultiplier,$QuiverMultiplier[[i,j]]];



(* ::Subsection:: *)
(*Data for common brane tilings*)


ListKnownBraneTilings:=Do[Print[i,":",BraneTilingsData[[i,1]]];,{i,Length[BraneTilingsData]}];
BraneTilingsData={
{"C^3",{{0,0},{0,1},{1,0}},{{{h1+h3/3,h2+h3/3,-h1-h2+h3/3}}},Phi[1,1,1] Phi[1,1,2] Phi[1,1,3],Phi[1,1,1] Phi[1,1,2] Phi[1,1,3],{-(1/2),Sqrt[3]/2},{1,0}},
{"Conifold=Y10",{{0,0},{0,1},{1,1},{1,0},{0,0},{1,1}},{{{},{h1+h3/4,-h1+h3/4}},{{h2+h3/4,-h2+h3/4},{}}},Phi[1,2,1] Phi[1,2,2] Phi[2,1,1] Phi[2,1,2],Phi[1,2,1] Phi[1,2,2] Phi[2,1,1] Phi[2,1,2],{-(1/2),Sqrt[3]/2},{1,0}},
{"C^2xC/2",{{0,1},{0,0},{1,0},{2,0},{0,1},{1,0}},{{{h1},{h2,-h1-h2+h3}},{{h2,-h1-h2+h3},{h1}}},Phi[1,1,1] Phi[1,2,2] Phi[2,1,1]+Phi[1,1,1] Phi[1,2,1] Phi[2,1,2],Phi[1,2,2] Phi[2,1,1] Phi[2,2,1]+Phi[1,2,1] Phi[2,1,2] Phi[2,2,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"C^2xC/3",{{0,1},{0,0},{1,0},{2,0},{3,0},{0,1},{1,0},{2,0},{0,1}},{{{h1},{h2},{-h1-h2+h3}},{{-h1-h2+h3},{h1},{h2}},{{h2},{-h1-h2+h3},{h1}}},Phi[1,1,1] Phi[1,2,1] Phi[2,1,1]+Phi[2,2,1] Phi[2,3,1] Phi[3,2,1]+Phi[1,3,1] Phi[3,1,1] Phi[3,3,1],Phi[1,2,1] Phi[2,1,1] Phi[2,2,1]+Phi[1,1,1] Phi[1,3,1] Phi[3,1,1]+Phi[2,3,1] Phi[3,2,1] Phi[3,3,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"C^3/2x2",{{0,0},{2,0},{0,2},{0,1},{1,0},{1,1},{0,1}},{{{},{h1},{h2},{-h1-h2+h3}},{{h1},{},{-h1-h2+h3},{h2}},{{h2},{-h1-h2+h3},{},{h1}},{{-h1-h2+h3},{h2},{h1},{}}},Phi[1,3,1] Phi[2,1,1] Phi[3,2,1]+Phi[1,2,1] Phi[2,4,1] Phi[4,1,1]+Phi[2,3,1] Phi[3,4,1] Phi[4,2,1]+Phi[1,4,1] Phi[3,1,1] Phi[4,3,1],Phi[1,2,1] Phi[2,3,1] Phi[3,1,1]+Phi[1,3,1] Phi[3,4,1] Phi[4,1,1]+Phi[1,4,1] Phi[2,1,1] Phi[4,2,1]+Phi[2,4,1] Phi[3,2,1] Phi[4,3,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"SPP=L121",{{0,0},{2,0},{1,1},{0,1},{0,0},{1,1},{1,0}},{{{-h1-h2+h3},{h1},{h2}},{{h2},{},{-h2+h3/2}},{{h1},{-h1+h3/2},{}}},Phi[1,1,1] Phi[1,3,1] Phi[3,1,1]+Phi[1,2,1] Phi[2,1,1] Phi[2,3,1] Phi[3,2,1],Phi[1,1,1] Phi[1,2,1] Phi[2,1,1]+Phi[1,3,1] Phi[2,3,1] Phi[3,1,1] Phi[3,2,1],{0,1},{1,0}},
{"L131",{{0,0},{1,-1},{1,0},{1,1},{1,2},{0,1}},{{{h2},{h1},{},{-h1-h2+h3}},{{-h1-h2+h3},{h2},{h1},{}},{{},{-h1-h2+h3},{},{h1+h2-h3/2}},{{h1},{},{-h1+h3/2},{}}},Phi[1,1,1] Phi[1,2,1] Phi[2,1,1]+Phi[2,2,1] Phi[2,3,1] Phi[3,2,1]+Phi[1,4,1] Phi[3,4,1] Phi[4,1,1] Phi[4,3,1],Phi[1,2,1] Phi[2,1,1] Phi[2,2,1]+Phi[1,1,1] Phi[1,4,1] Phi[4,1,1]+Phi[2,3,1] Phi[3,2,1] Phi[3,4,1] Phi[4,3,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"P2=C^3/(1,1,1)",{{0,0},{1,0},{0,1},{-1,-1},{1,0},{0,1},{0,0},{-1,-1}},{{{},{h1,h2,-h1-h2+h3},{}},{{},{},{h1,h2,-h1-h2+h3}},{{h1,h2,-h1-h2+h3},{},{}}},Phi[1,2,2] Phi[2,3,3] Phi[3,1,1]+Phi[1,2,3] Phi[2,3,1] Phi[3,1,2]+Phi[1,2,1] Phi[2,3,2] Phi[3,1,3],Phi[1,2,3] Phi[2,3,2] Phi[3,1,1]+Phi[1,2,1] Phi[2,3,3] Phi[3,1,2]+Phi[1,2,2] Phi[2,3,1] Phi[3,1,3],{-(1/2),Sqrt[3]/2},{1,0}},
{"F0.1=P1xP1",{{1,0},{0,1},{-1,0},{0,-1},{1,0},{-1,0},{0,1},{0,-1}},{{{},{h1,-h1+(2 h3)/3},{h2,-h2+(2 h3)/3},{}},{{},{},{},{h2,-h2+(2 h3)/3}},{{},{},{},{h1,-h1+(2 h3)/3}},{{h1+h2-h3/3,h1-h2+h3/3,-h1+h2+h3/3,-h1-h2+h3},{},{},{}}},Phi[1,2,2] Phi[2,4,2] Phi[4,1,1]+Phi[1,3,1] Phi[3,4,2] Phi[4,1,2]+Phi[1,3,2] Phi[3,4,1] Phi[4,1,3]+Phi[1,2,1] Phi[2,4,1] Phi[4,1,4],Phi[1,3,2] Phi[3,4,2] Phi[4,1,1]+Phi[1,2,2] Phi[2,4,1] Phi[4,1,2]+Phi[1,2,1] Phi[2,4,2] Phi[4,1,3]+Phi[1,3,1] Phi[3,4,1] Phi[4,1,4],{-(1/2),Sqrt[3]/2},{1,0}},
{"F0.2=P1xP1",{{1,0},{0,1},{-1,0},{0,-1},{1,0},{-1,0},{0,1},{0,-1}},{{{},{h1,-h1+h3/2},{},{}},{{},{},{h2,-h2+h3/2},{}},{{},{},{},{h1,-h1+h3/2}},{{h2,-h2+h3/2},{},{},{}}},Phi[1,2,1] Phi[2,3,2] Phi[3,4,2] Phi[4,1,1]+Phi[1,2,1] Phi[2,3,1] Phi[3,4,2] Phi[4,1,2],Phi[1,2,2] Phi[2,3,2] Phi[3,4,1] Phi[4,1,1]+Phi[1,2,2] Phi[2,3,1] Phi[3,4,1] Phi[4,1,2],{-(1/2),Sqrt[3]/2},{1,0}},
{"F1=dP1=Y21=L312",{{1,0},{0,1},{-1,1},{0,-1},{1,0}},{{{},{h1},{-((2 h1)/3)+h3/2},{}},{{},{},{h2,h1/3-h2+h3/2},{}},{{},{},{},{h1/3+h2,-((4 h1)/3)+h3/2,(2 h1)/3-h2+h3/2}},{{h2,h1/3-h2+h3/2},{-((2 h1)/3)+h3/2},{},{}}},Phi[1,2,1] Phi[2,3,2] Phi[3,4,2] Phi[4,1,1]+Phi[1,3,1] Phi[3,4,1] Phi[4,1,2]+Phi[2,3,1] Phi[3,4,3] Phi[4,2,1],Phi[1,3,1] Phi[3,4,3] Phi[4,1,1]+Phi[1,2,1] Phi[2,3,1] Phi[3,4,2] Phi[4,1,2]+Phi[2,3,2] Phi[3,4,1] Phi[4,2,1],{0,1},{1,0.2}},
{"F2=C^3/(1,1,2)",{{1,0},{0,1},{-1,2},{0,-1},{1,0}},{{{},{h1,h2},{-h1-h2+h3},{}},{{},{},{h1,h2},{-h1-h2+h3}},{{-h1-h2+h3},{},{},{h1,h2}},{{h1,h2},{-h1-h2+h3},{},{}}},Phi[1,2,1] Phi[2,3,2] Phi[3,1,1]+Phi[1,2,2] Phi[2,4,1] Phi[4,1,1]+Phi[1,3,1] Phi[3,4,1] Phi[4,1,2]+Phi[2,3,1] Phi[3,4,2] Phi[4,2,1],Phi[1,2,2] Phi[2,3,1] Phi[3,1,1]+Phi[1,3,1] Phi[3,4,2] Phi[4,1,1]+Phi[1,2,1] Phi[2,4,1] Phi[4,1,2]+Phi[2,3,2] Phi[3,4,1] Phi[4,2,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"dP2.1",{{1,0},{0,1},{-1,0},{-1,-1},{0,-1}},{{{},{h1},{h2},{},{}},{{},{},{},{2 h1+3 h2-h3,-((8 h1)/3)-(11 h2)/3+2 h3},{}},{{},{},{},{3 h1+2 h2-h3,-((11 h1)/3)-(8 h2)/3+2 h3},{}},{{-3 h1-3 h2+2 h3},{},{},{},{-(h1/3)-(7 h2)/3+h3,-((7 h1)/3)-h2/3+h3,(13 h1)/3+(13 h2)/3-2 h3}},{{4 h1+4 h2-2 h3},{-((5 h1)/3)-(2 h2)/3+h3},{-((2 h1)/3)-(5 h2)/3+h3},{},{}}},Phi[1,3,1] Phi[3,4,1] Phi[4,1,1]+Phi[1,2,1] Phi[2,4,2] Phi[4,5,2] Phi[5,1,1]+Phi[2,4,1] Phi[4,5,1] Phi[5,2,1]+Phi[3,4,2] Phi[4,5,3] Phi[5,3,1],Phi[1,2,1] Phi[2,4,1] Phi[4,1,1]+Phi[1,3,1] Phi[3,4,2] Phi[4,5,1] Phi[5,1,1]+Phi[2,4,2] Phi[4,5,3] Phi[5,2,1]+Phi[3,4,1] Phi[4,5,2] Phi[5,3,1],{-(1/3),1},{1,0}},
{"dP2.2",{{1,0},{0,1},{-1,0},{-1,-1},{0,-1}},{{{},{h1,h2},{},{},{}},{{},{},{-2 h1-3 h2+(3 h3)/2,h1+2 h2-h3/2},{(4 h1)/5+(2 h2)/5+h3/10},{}},{{},{},{},{-((6 h1)/5)-(3 h2)/5+(3 h3)/5},{h1/5-(2 h2)/5+(2 h3)/5}},{{-((4 h1)/5)-(7 h2)/5+(9 h3)/10},{},{},{},{(2 h1)/5+(6 h2)/5-h3/5}},{{(9 h1)/5+(12 h2)/5-(9 h3)/10},{-((6 h1)/5)-(8 h2)/5+(11 h3)/10},{},{},{}}},Phi[1,2,1] Phi[2,3,2] Phi[3,4,1] Phi[4,1,1]+Phi[1,2,2] Phi[2,3,1] Phi[3,5,1] Phi[5,1,1]+Phi[2,4,1] Phi[4,5,1] Phi[5,2,1],Phi[1,2,2] Phi[2,4,1] Phi[4,1,1]+Phi[1,2,1] Phi[2,3,1] Phi[3,4,1] Phi[4,5,1] Phi[5,1,1]+Phi[2,3,2] Phi[3,5,1] Phi[5,2,1],{0,1},{3/2,-(1/3)}},
{"dP3.1",{{1,0},{1,1},{0,1},{-1,0},{-1,-1},{0,-1}},{{{},{h1},{h2},{},{},{}},{{},{},{-h1-3 h2+(4 h3)/3},{h1+2 h2-h3/2},{},{}},{{},{},{},{-2 h1-3 h2+(3 h3)/2},{h1+h2-h3/6},{}},{{},{},{},{},{-h1+h3/3},{-h2+(2 h3)/3}},{{-h1-2 h2+(7 h3)/6},{},{},{},{},{h1+3 h2-h3}},{{2 h1+3 h2-(7 h3)/6},{-h1-h2+(5 h3)/6},{},{},{},{}}},Phi[1,3,1] Phi[3,5,1] Phi[5,1,1]+Phi[1,2,1] Phi[2,3,1] Phi[3,4,1] Phi[4,5,1] Phi[5,6,1] Phi[6,1,1]+Phi[2,4,1] Phi[4,6,1] Phi[6,2,1],Phi[1,2,1] Phi[2,4,1] Phi[4,5,1] Phi[5,1,1]+Phi[1,3,1] Phi[3,4,1] Phi[4,6,1] Phi[6,1,1]+Phi[2,3,1] Phi[3,5,1] Phi[5,6,1] Phi[6,2,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"dP3.2",{{1,0},{1,1},{0,1},{-1,0},{-1,-1},{0,-1}},{{{},{h1,-h1+h3/2},{h2},{},{},{}},{{},{},{-2 h2+(7 h3)/8},{h1/2+h2/2+h3/16},{-(h1/2)+h2/2+(5 h3)/16},{}},{{},{},{},{-(h1/2)-h2/2+(9 h3)/16},{h1/2-h2/2+(5 h3)/16},{}},{{h1/2-h2/2+(7 h3)/16},{},{},{},{},{-(h1/2)+h2/2+(3 h3)/16}},{{-(h1/2)-h2/2+(11 h3)/16},{},{},{},{},{h1/2+h2/2-h3/16}},{{2 h2-(5 h3)/8},{-h2+(3 h3)/4},{},{},{},{}}},Phi[1,2,2] Phi[2,4,1] Phi[4,1,1]+Phi[1,3,1] Phi[3,5,1] Phi[5,1,1]+Phi[1,2,1] Phi[2,3,1] Phi[3,4,1] Phi[4,6,1] Phi[6,1,1]+Phi[2,5,1] Phi[5,6,1] Phi[6,2,1],Phi[1,3,1] Phi[3,4,1] Phi[4,1,1]+Phi[1,2,1] Phi[2,5,1] Phi[5,1,1]+Phi[1,2,2] Phi[2,3,1] Phi[3,5,1] Phi[5,6,1] Phi[6,1,1]+Phi[2,4,1] Phi[4,6,1] Phi[6,2,1],{0,3/2},{1,0}},
{"dP3.3",{{1,0},{1,1},{0,1},{-1,0},{-1,-1},{0,-1}},{{{},{h1,-h1+(2 h3)/5},{h2},{-h2+(4 h3)/5},{},{}},{{},{},{-h2+(3 h3)/5},{h2-h3/5},{},{}},{{},{},{},{},{-(h1/2)+(2 h3)/5},{h1/2+h3/5}},{{},{},{},{},{h1/2+h3/5},{-(h1/2)+(2 h3)/5}},{{h1/2-h2+(3 h3)/5,-(h1/2)+h2},{},{},{},{},{}},{{-(h1/2)-h2+(4 h3)/5,h1/2+h2-h3/5},{},{},{},{},{}}},Phi[1,3,1] Phi[3,5,1] Phi[5,1,1]+Phi[1,2,2] Phi[2,4,1] Phi[4,5,1] Phi[5,1,1]+Phi[1,2,2] Phi[2,3,1] Phi[3,6,1] Phi[6,1,2]+Phi[1,4,1] Phi[4,6,1] Phi[6,1,2],Phi[1,2,1] Phi[2,3,1] Phi[3,5,1] Phi[5,1,2]+Phi[1,4,1] Phi[4,5,1] Phi[5,1,2]+Phi[1,3,1] Phi[3,6,1] Phi[6,1,1]+Phi[1,2,1] Phi[2,4,1] Phi[4,6,1] Phi[6,1,1],{0,2},{1,0}},
{"dP3.4",{{1,0},{1,1},{0,1},{-1,0},{-1,-1},{0,-1}},{{{},{h1,h2,-h1-h2+h3},{-h1+(2 h3)/3,-h2+(2 h3)/3,h1+h2-h3/3},{},{},{}},{{},{},{},{-(h1/2)-h2/2+(2 h3)/3},{h2/2+h3/6},{h1/2+h3/6}},{{},{},{},{h1/2+h2/2},{-(h2/2)+h3/2},{-(h1/2)+h3/2}},{{-(h1/2)+h2/2+h3/3,h1/2-h2/2+h3/3},{},{},{},{},{}},{{h1+h2/2-h3/6,-h1-h2/2+(5 h3)/6},{},{},{},{},{}},{{-(h1/2)-h2+(5 h3)/6,h1/2+h2-h3/6},{},{},{},{},{}}},Phi[1,2,1] Phi[2,4,1] Phi[4,1,1]+Phi[1,3,1] Phi[3,4,1] Phi[4,1,2]+Phi[1,2,3] Phi[2,5,1] Phi[5,1,1]+Phi[1,3,3] Phi[3,5,1] Phi[5,1,2]+Phi[1,2,2] Phi[2,6,1] Phi[6,1,1]+Phi[1,3,2] Phi[3,6,1] Phi[6,1,2],Phi[1,3,2] Phi[3,4,1] Phi[4,1,1]+Phi[1,2,2] Phi[2,4,1] Phi[4,1,2]+Phi[1,3,1] Phi[3,5,1] Phi[5,1,1]+Phi[1,2,1] Phi[2,5,1] Phi[5,1,2]+Phi[1,3,3] Phi[3,6,1] Phi[6,1,1]+Phi[1,2,3] Phi[2,6,1] Phi[6,1,2],{-(1/2),Sqrt[3]/2},{1,0}},
{"PdP2",{{1,0},{-1,1},{-1,0},{-1,-1},{0,-1}},{{{},{h1,h2},{-h1-h2+h3},{},{}},{{},{},{h1,h2},{-((3 h1)/5)-h2+(4 h3)/5},{}},{{-h1-h2+h3},{},{},{(2 h1)/5+h2-h3/5},{(3 h1)/5+h3/5}},{{(3 h1)/5+h3/5},{},{},{},{-((4 h1)/5)+(2 h3)/5}},{{(2 h1)/5+h2-h3/5},{-((3 h1)/5)-h2+(4 h3)/5},{},{},{}}},Phi[1,2,2] Phi[2,3,1] Phi[3,1,1]+Phi[1,3,1] Phi[3,4,1] Phi[4,1,1]+Phi[1,3,1] Phi[3,5,1] Phi[5,1,1]+Phi[2,3,1] Phi[3,4,1] Phi[4,5,1] Phi[5,2,1],Phi[1,2,1] Phi[2,3,2] Phi[3,1,1]+Phi[1,2,2] Phi[2,4,1] Phi[4,1,1]+Phi[1,2,1] Phi[2,4,1] Phi[4,5,1] Phi[5,1,1]+Phi[2,3,2] Phi[3,5,1] Phi[5,2,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"PdP3a=C^3/(1,2,3)",{{-1,0},{0,-1},{2,3}},{{{},{h1},{h2},{-h1-h2+h3},{},{}},{{},{},{h1},{h2},{-h1-h2+h3},{}},{{},{},{},{h1},{h2},{-h1-h2+h3}},{{-h1-h2+h3},{},{},{},{h1},{h2}},{{h2},{-h1-h2+h3},{},{},{},{h1}},{{h1},{h2},{-h1-h2+h3},{},{},{}}},Phi[1,2,1] Phi[2,4,1] Phi[4,1,1]+Phi[1,4,1] Phi[4,5,1] Phi[5,1,1]+Phi[2,3,1] Phi[3,5,1] Phi[5,2,1]+Phi[1,3,1] Phi[3,6,1] Phi[6,1,1]+Phi[2,5,1] Phi[5,6,1] Phi[6,2,1]+Phi[3,4,1] Phi[4,6,1] Phi[6,3,1],Phi[1,3,1] Phi[3,4,1] Phi[4,1,1]+Phi[1,2,1] Phi[2,5,1] Phi[5,1,1]+Phi[2,4,1] Phi[4,5,1] Phi[5,2,1]+Phi[1,4,1] Phi[4,6,1] Phi[6,1,1]+Phi[2,3,1] Phi[3,6,1] Phi[6,2,1]+Phi[3,5,1] Phi[5,6,1] Phi[6,3,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"PdP3b",{{1,0},{0,1},{-1,1},{-1,0},{-1,-1},{0,-1}},{{{},{h1},{h2},{-h1-h2+h3},{},{}},{{h1},{},{},{},{h1/3+h2},{-((4 h1)/3)-h2+h3}},{{},{-h1-h2+h3},{},{(5 h1)/3+2 h2-h3},{},{}},{{},{h2},{},{},{},{(2 h1)/3}},{{-((4 h1)/3)-h2+h3},{},{(2 h1)/3},{},{},{}},{{h1/3+h2},{},{},{},{-h1-2 h2+h3},{}}},Phi[1,4,1] Phi[2,1,1] Phi[4,2,1]+Phi[2,5,1] Phi[3,2,1] Phi[5,3,1]+Phi[1,2,1] Phi[2,6,1] Phi[6,1,1]+Phi[1,3,1] Phi[3,4,1] Phi[4,6,1] Phi[5,1,1] Phi[6,5,1],Phi[1,3,1] Phi[2,1,1] Phi[3,2,1]+Phi[1,2,1] Phi[2,5,1] Phi[5,1,1]+Phi[1,4,1] Phi[4,6,1] Phi[6,1,1]+Phi[2,6,1] Phi[3,4,1] Phi[4,2,1] Phi[5,3,1] Phi[6,5,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"PdP3c=SPP/2",{{1,0},{0,1},{-1,2},{-1,1},{-1,0},{0,-1}},{{{},{},{h1},{},{},{-h1+h3/2}},{{h2},{},{},{},{-h2+h3/2},{}},{{},{},{},{h2},{},{-h2+h3/2}},{{},{h1},{},{},{-h1+h3/2},{}},{{-h2+h3/2},{},{-h1+h3/2},{},{},{h1+h2}},{{},{-h1+h3/2},{},{-h2+h3/2},{h1+h2},{}}},Phi[1,3,1] Phi[3,4,1] Phi[4,5,1] Phi[5,1,1]+Phi[2,5,1] Phi[5,6,1] Phi[6,2,1]+Phi[1,6,1] Phi[2,1,1] Phi[4,2,1] Phi[6,4,1]+Phi[3,6,1] Phi[5,3,1] Phi[6,5,1],Phi[2,5,1] Phi[3,4,1] Phi[4,2,1] Phi[5,3,1]+Phi[1,3,1] Phi[2,1,1] Phi[3,6,1] Phi[6,2,1]+Phi[4,5,1] Phi[5,6,1] Phi[6,4,1]+Phi[1,6,1] Phi[5,1,1] Phi[6,5,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"PdP4a",{{1,0},{0,1},{-1,2},{-1,1},{-1,0},{0,-1},{1,-1}},{{{},{},{h2},{},{},{h1},{}},{{},{},{(35 h1)/4+(39 h2)/4-(23 h3)/4},{},{},{-((31 h1)/4)-(35 h2)/4+(23 h3)/4},{}},{{},{},{},{(5 h1)/2+(9 h2)/2-2 h3,-12 h1-16 h2+(19 h3)/2},{},{},{11 h1+13 h2-(15 h3)/2}},{{12 h1+15 h2-(17 h3)/2},{-((45 h1)/4)-(57 h2)/4+(35 h3)/4},{},{},{(19 h1)/4+(19 h2)/4-(11 h3)/4},{},{-9 h1-9 h2+6 h3}},{{},{},{-((29 h1)/4)-(37 h2)/4+(23 h3)/4},{},{},{(33 h1)/4+(41 h2)/4-(23 h3)/4},{}},{{},{},{},{19 h1+23 h2-(27 h3)/2,-13 h1-15 h2+(19 h3)/2},{},{},{-((9 h1)/2)-(13 h2)/2+4 h3}},{{-11 h1-14 h2+(17 h3)/2},{(49 h1)/4+(61 h2)/4-(35 h3)/4},{},{},{-((15 h1)/4)-(15 h2)/4+(11 h3)/4},{},{}}},Phi[1,3,1] Phi[3,4,2] Phi[4,1,1]+Phi[2,3,1] Phi[3,4,1] Phi[4,2,1]+Phi[4,5,1] Phi[5,6,1] Phi[6,4,2]+Phi[1,6,1] Phi[4,7,1] Phi[6,4,1] Phi[7,1,1]+Phi[2,6,1] Phi[6,7,1] Phi[7,2,1]+Phi[3,7,1] Phi[5,3,1] Phi[7,5,1],Phi[3,4,1] Phi[4,5,1] Phi[5,3,1]+Phi[2,6,1] Phi[4,2,1] Phi[6,4,1]+Phi[1,6,1] Phi[4,1,1] Phi[6,4,2]+Phi[1,3,1] Phi[3,7,1] Phi[7,1,1]+Phi[2,3,1] Phi[3,4,2] Phi[4,7,1] Phi[7,2,1]+Phi[5,6,1] Phi[6,7,1] Phi[7,5,1],{0,2},{1,-1}},
{"PdP4b",{{1,0},{0,1},{-1,2},{-1,1},{-1,0},{-1,-1},{0,-1}},{{{},{},{h2},{},{},{h1},{-((3 h1)/4)-h2+(7 h3)/8}},{{-(h1/4)+h2+h3/8},{},{},{},{(5 h1)/4-h3/8},{-((3 h1)/4)-h2+(7 h3)/8},{}},{{},{},{},{-h1+h3/2},{},{},{(3 h1)/4+h3/8}},{{},{h2},{},{},{-(h1/4)-h2+(5 h3)/8},{},{}},{{(5 h1)/4-h3/8},{},{-(h1/4)-h2+(5 h3)/8},{},{},{-(h1/2)+h2+h3/4},{}},{{},{-((3 h1)/4)-h2+(7 h3)/8},{},{(3 h1)/4+h3/8},{},{},{-(h1/4)+h2+h3/8}},{{-((3 h1)/4)-h2+(7 h3)/8},{h1},{},{},{-(h1/2)+h2+h3/4},{},{}}},Phi[1,3,1] Phi[3,4,1] Phi[4,5,1] Phi[5,1,1]+Phi[2,5,1] Phi[5,6,1] Phi[6,2,1]+Phi[2,6,1] Phi[4,2,1] Phi[6,4,1]+Phi[1,6,1] Phi[6,7,1] Phi[7,1,1]+Phi[1,7,1] Phi[2,1,1] Phi[7,2,1]+Phi[3,7,1] Phi[5,3,1] Phi[7,5,1],Phi[2,5,1] Phi[3,4,1] Phi[4,2,1] Phi[5,3,1]+Phi[1,6,1] Phi[2,1,1] Phi[6,2,1]+Phi[4,5,1] Phi[5,6,1] Phi[6,4,1]+Phi[1,3,1] Phi[3,7,1] Phi[7,1,1]+Phi[2,6,1] Phi[6,7,1] Phi[7,2,1]+Phi[1,7,1] Phi[5,1,1] Phi[7,5,1],{0,1},{1,0}},
{"PdP5a=Conifold/2x2",{{1,0},{1,1},{0,1},{-1,1},{-1,0},{-1,-1},{0,-1},{1,-1}},{{{},{},{h1},{-h1+h3/2},{},{},{},{}},{{},{},{-h1+h3/2},{h1},{},{},{},{}},{{},{},{},{},{h2},{-h2+h3/2},{},{}},{{},{},{},{},{-h2+h3/2},{h2},{},{}},{{},{},{},{},{},{},{-h1+h3/2},{h1}},{{},{},{},{},{},{},{h1},{-h1+h3/2}},{{-h2+h3/2},{h2},{},{},{},{},{},{}},{{h2},{-h2+h3/2},{},{},{},{},{},{}}},Phi[1,4,1] Phi[4,6,1] Phi[6,7,1] Phi[7,1,1]+Phi[2,4,1] Phi[4,5,1] Phi[5,7,1] Phi[7,2,1]+Phi[1,3,1] Phi[3,6,1] Phi[6,8,1] Phi[8,1,1]+Phi[2,3,1] Phi[3,5,1] Phi[5,8,1] Phi[8,2,1],Phi[1,3,1] Phi[3,5,1] Phi[5,7,1] Phi[7,1,1]+Phi[2,3,1] Phi[3,6,1] Phi[6,7,1] Phi[7,2,1]+Phi[1,4,1] Phi[4,5,1] Phi[5,8,1] Phi[8,1,1]+Phi[2,4,1] Phi[4,6,1] Phi[6,8,1] Phi[8,2,1],{0,1},{1,0}},
{"PdP5b=L131/2",{{1,0},{0,1},{-1,2},{-1,1},{-1,0},{-1,-1},{0,-1},{1,-1},{1,0}},{{{},{},{},{h1},{},{},{h2},{-((4 h1)/5)-(4 h2)/5+(4 h3)/5}},{{},{},{-(h1/4)-(3 h2)/4+h3/2},{},{},{h1/20+(11 h2)/20+h3/5},{},{}},{{h1},{},{},{-((3 h1)/10)+(7 h2)/10+(3 h3)/10},{},{},{-((3 h1)/5)-(3 h2)/5+(3 h3)/5},{}},{{},{(11 h1)/20+h2/20+h3/5},{},{},{-(h1/4)-(3 h2)/4+h3/2},{},{},{-(h1/5)+(4 h2)/5+h3/5}},{{},{},{(11 h1)/20+h2/20+h3/5},{},{},{-((3 h1)/4)-h2/4+h3/2},{},{}},{{h2},{},{},{-((3 h1)/5)-(3 h2)/5+(3 h3)/5},{},{},{(7 h1)/10-(3 h2)/10+(3 h3)/10},{}},{{},{-((3 h1)/4)-h2/4+h3/2},{},{},{h1/20+(11 h2)/20+h3/5},{},{},{(4 h1)/5-h2/5+h3/5}},{{-((4 h1)/5)-(4 h2)/5+(4 h3)/5},{},{-(h1/5)+(4 h2)/5+h3/5},{},{},{(4 h1)/5-h2/5+h3/5},{},{}}},Phi[2,3,1] Phi[3,4,1] Phi[4,2,1]+Phi[1,4,1] Phi[4,5,1] Phi[5,6,1] Phi[6,1,1]+Phi[2,6,1] Phi[6,7,1] Phi[7,2,1]+Phi[3,7,1] Phi[5,3,1] Phi[7,5,1]+Phi[1,7,1] Phi[7,8,1] Phi[8,1,1]+Phi[1,8,1] Phi[3,1,1] Phi[8,3,1]+Phi[4,8,1] Phi[6,4,1] Phi[8,6,1],Phi[3,4,1] Phi[4,5,1] Phi[5,3,1]+Phi[2,6,1] Phi[4,2,1] Phi[6,4,1]+Phi[1,7,1] Phi[2,3,1] Phi[3,1,1] Phi[7,2,1]+Phi[5,6,1] Phi[6,7,1] Phi[7,5,1]+Phi[1,4,1] Phi[4,8,1] Phi[8,1,1]+Phi[3,7,1] Phi[7,8,1] Phi[8,3,1]+Phi[1,8,1] Phi[6,1,1] Phi[8,6,1],{0,1},{1,0}},
{"PdP5c=C^3/4x2",{{1,0},{0,1},{-1,2},{-1,1},{-1,0},{-1,-1},{-1,-2},{0,-1}},{{{},{h1},{},{h2},{},{},{-h1-h2+h3},{}},{{h1},{},{h2},{},{},{},{},{-h1-h2+h3}},{{-h1-h2+h3},{},{},{h1},{},{h2},{},{}},{{},{-h1-h2+h3},{h1},{},{h2},{},{},{}},{{},{},{-h1-h2+h3},{},{},{h1},{},{h2}},{{},{},{},{-h1-h2+h3},{h1},{},{h2},{}},{{},{h2},{},{},{-h1-h2+h3},{},{},{h1}},{{h2},{},{},{},{},{-h1-h2+h3},{h1},{}}},Phi[2,3,1] Phi[3,4,1] Phi[4,2,1]+Phi[1,4,1] Phi[3,1,1] Phi[4,3,1]+Phi[4,5,1] Phi[5,6,1] Phi[6,4,1]+Phi[3,6,1] Phi[5,3,1] Phi[6,5,1]+Phi[1,7,1] Phi[2,1,1] Phi[7,2,1]+Phi[1,2,1] Phi[2,8,1] Phi[8,1,1]+Phi[6,7,1] Phi[7,8,1] Phi[8,6,1]+Phi[5,8,1] Phi[7,5,1] Phi[8,7,1],Phi[1,2,1] Phi[2,3,1] Phi[3,1,1]+Phi[1,4,1] Phi[2,1,1] Phi[4,2,1]+Phi[3,4,1] Phi[4,5,1] Phi[5,3,1]+Phi[3,6,1] Phi[4,3,1] Phi[6,4,1]+Phi[5,6,1] Phi[6,7,1] Phi[7,5,1]+Phi[1,7,1] Phi[7,8,1] Phi[8,1,1]+Phi[5,8,1] Phi[6,5,1] Phi[8,6,1]+Phi[2,8,1] Phi[7,2,1] Phi[8,7,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"PdP6=C^3/3x3",{{2,-1},{1,0},{0,1},{-1,2},{-1,1},{-1,0},{-1,-1},{0,-1},{1,-1}},{{{},{h1},{},{},{h2},{},{},{-h1-h2+h3},{}},{{},{},{-h1-h2+h3},{},{},{h1},{},{},{h2}},{{h2},{},{},{h1},{},{},{-h1-h2+h3},{},{}},{{},{h2},{},{},{-h1-h2+h3},{},{},{h1},{}},{{},{},{h2},{},{},{-h1-h2+h3},{},{},{h1}},{{h1},{},{},{-h1-h2+h3},{},{},{h2},{},{}},{{},{-h1-h2+h3},{},{},{h1},{},{},{h2},{}},{{},{},{h1},{},{},{h2},{},{},{-h1-h2+h3}},{{-h1-h2+h3},{},{},{h2},{},{},{h1},{},{}}},Phi[2,3,1] Phi[3,4,1] Phi[4,2,1]+Phi[1,5,1] Phi[5,6,1] Phi[6,1,1]+Phi[2,6,1] Phi[6,7,1] Phi[7,2,1]+Phi[3,7,1] Phi[5,3,1] Phi[7,5,1]+Phi[1,8,1] Phi[3,1,1] Phi[8,3,1]+Phi[4,8,1] Phi[6,4,1] Phi[8,6,1]+Phi[1,2,1] Phi[2,9,1] Phi[9,1,1]+Phi[4,5,1] Phi[5,9,1] Phi[9,4,1]+Phi[7,8,1] Phi[8,9,1] Phi[9,7,1],Phi[1,2,1] Phi[2,3,1] Phi[3,1,1]+Phi[3,4,1] Phi[4,5,1] Phi[5,3,1]+Phi[2,6,1] Phi[4,2,1] Phi[6,4,1]+Phi[5,6,1] Phi[6,7,1] Phi[7,5,1]+Phi[3,7,1] Phi[7,8,1] Phi[8,3,1]+Phi[1,8,1] Phi[6,1,1] Phi[8,6,1]+Phi[1,5,1] Phi[5,9,1] Phi[9,1,1]+Phi[4,8,1] Phi[8,9,1] Phi[9,4,1]+Phi[2,9,1] Phi[7,2,1] Phi[9,7,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"L152",{{-1,-1},{0,-1},{2,0},{0,1}},{{{},{h1,h2},{},{-((13 h1)/14)-h2+(27 h3)/28},{},{}},{{},{},{-(h1/7)+h2+h3/14,(6 h1)/7+h3/14},{},{},{-((4 h1)/7)-h2+(11 h3)/14}},{{-((6 h1)/7)-h2+(13 h3)/14},{},{},{h2,h1},{},{}},{{},{-((6 h1)/7)-h2+(13 h3)/14},{},{},{(4 h1)/7+(3 h3)/14},{(5 h1)/14+h2-(5 h3)/28}},{{(5 h1)/14+h2-(5 h3)/28},{},{-((4 h1)/7)-h2+(11 h3)/14},{},{},{}},{{(4 h1)/7+(3 h3)/14},{},{},{},{-((11 h1)/14)+(11 h3)/28},{}}},Phi[1,2,1] Phi[2,3,1] Phi[3,1,1]+Phi[2,3,2] Phi[3,4,1] Phi[4,2,1]+Phi[1,4,1] Phi[4,5,1] Phi[5,1,1]+Phi[1,2,2] Phi[2,6,1] Phi[6,1,1]+Phi[3,4,2] Phi[4,6,1] Phi[5,3,1] Phi[6,5,1],Phi[1,2,2] Phi[2,3,2] Phi[3,1,1]+Phi[2,3,1] Phi[3,4,2] Phi[4,2,1]+Phi[3,4,1] Phi[4,5,1] Phi[5,3,1]+Phi[1,4,1] Phi[4,6,1] Phi[6,1,1]+Phi[1,2,1] Phi[2,6,1] Phi[5,1,1] Phi[6,5,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"Y32=L153",{{-1,0},{-1,-1},{0,-1},{2,2}},{{{},{h1,h2},{},{},{},{}},{{},{},{(7 h1)/4+(3 h2)/4-(3 h3)/8,(3 h1)/4+(7 h2)/4-(3 h3)/8},{},{-((15 h1)/4)-(15 h2)/4+(19 h3)/8},{}},{{-((7 h1)/4)-(7 h2)/4+(11 h3)/8},{},{},{(3 h1)/2+h2/2-h3/4,h1/2+(3 h2)/2-h3/4},{},{}},{{},{-((9 h1)/4)-(9 h2)/4+(13 h3)/8},{},{},{(7 h1)/4+(3 h2)/4-(3 h3)/8,(3 h1)/4+(7 h2)/4-(3 h3)/8},{}},{{},{},{-((9 h1)/4)-(9 h2)/4+(13 h3)/8},{},{},{h1,h2}},{{(11 h1)/4+(11 h2)/4-(11 h3)/8},{},{},{-((7 h1)/4)-(7 h2)/4+(11 h3)/8},{},{}}},Phi[1,2,1] Phi[2,3,2] Phi[3,1,1]+Phi[2,3,1] Phi[3,4,2] Phi[4,2,1]+Phi[3,4,1] Phi[4,5,2] Phi[5,3,1]+Phi[1,2,2] Phi[2,5,1] Phi[5,6,1] Phi[6,1,1]+Phi[4,5,1] Phi[5,6,2] Phi[6,4,1],Phi[1,2,2] Phi[2,3,1] Phi[3,1,1]+Phi[2,3,2] Phi[3,4,1] Phi[4,2,1]+Phi[3,4,2] Phi[4,5,1] Phi[5,3,1]+Phi[1,2,1] Phi[2,5,1] Phi[5,6,2] Phi[6,1,1]+Phi[4,5,2] Phi[5,6,1] Phi[6,4,1],{1/2,Sqrt[3]/2},{1,0}},
{"C^3/(1,1,3)",{{-1,0},{0,-1},{2,2}},{{{},{h1,h2},{},{-h1-h2+h3},{}},{{},{},{h1,h2},{},{-h1-h2+h3}},{{-h1-h2+h3},{},{},{h1,h2},{}},{{},{-h1-h2+h3},{},{},{h1,h2}},{{h1,h2},{},{-h1-h2+h3},{},{}}},Phi[1,2,1] Phi[2,3,2] Phi[3,1,1]+Phi[2,3,1] Phi[3,4,2] Phi[4,2,1]+Phi[1,2,2] Phi[2,5,1] Phi[5,1,1]+Phi[1,4,1] Phi[4,5,1] Phi[5,1,2]+Phi[3,4,1] Phi[4,5,2] Phi[5,3,1],Phi[1,2,2] Phi[2,3,1] Phi[3,1,1]+Phi[2,3,2] Phi[3,4,1] Phi[4,2,1]+Phi[1,4,1] Phi[4,5,2] Phi[5,1,1]+Phi[1,2,1] Phi[2,5,1] Phi[5,1,2]+Phi[3,4,2] Phi[4,5,1] Phi[5,3,1],{-(1/2),Sqrt[3]/2},{1,0}},
{"C^3/(1,1,4)",{{-1,0},{0,-1},{1,4}},{{{},{h1,h2},{},{},{-h1-h2+h3},{}},{{},{},{h1,h2},{},{},{-h1-h2+h3}},{{-h1-h2+h3},{},{},{h1,h2},{},{}},{{},{-h1-h2+h3},{},{},{h1,h2},{}},{{},{},{-h1-h2+h3},{},{},{h1,h2}},{{h1,h2},{},{},{-h1-h2+h3},{},{}}},Phi[1,2,1] Phi[2,3,2] Phi[3,1,1]+Phi[2,3,1] Phi[3,4,2] Phi[4,2,1]+Phi[3,4,1] Phi[4,5,2] Phi[5,3,1]+Phi[1,2,2] Phi[2,6,1] Phi[6,1,1]+Phi[1,5,1] Phi[5,6,1] Phi[6,1,2]+Phi[4,5,1] Phi[5,6,2] Phi[6,4,1],Phi[1,2,2] Phi[2,3,1] Phi[3,1,1]+Phi[2,3,2] Phi[3,4,1] Phi[4,2,1]+Phi[3,4,2] Phi[4,5,1] Phi[5,3,1]+Phi[1,5,1] Phi[5,6,2] Phi[6,1,1]+Phi[1,2,1] Phi[2,6,1] Phi[6,1,2]+Phi[4,5,2] Phi[5,6,1] Phi[6,4,1],{-(1/2),Sqrt[3]/2},{1,0}}
};



End[];
EndPackage[]
