(* ::Package:: *)

(*********************************************************************
 *                                                                 
 *  CoulombHiggs.m  v. 1.1                 
 *                                                          
 *  Copyright J. Manschot, B. Pioline and A. Sen, Feb 2013
 *
 *  Distributed under the terms of the GNU General Public License 
 *
 * v 1.1: changed TestNoLoop
 *
 *********************************************************************)
Print["CoulombHiggs v 1.1 - A package for evaluating quiver invariants using the Coulomb and Higgs branch formulae."];


BeginPackage["CoulombHiggs`"]

(** symbols **)

y::usage = "Angular momentum fugacity";

Om::usage = "Om[gam_,y_] denotes the integer valued BPS index";

Omb::usage = "Omb[gam_,y_] denotes the rational BPS index";

OmT::usage = "OmT[gam_,y_] denotes the total single centered degeneracy with charge gam";

OmS::usage = "OmS[gam_,y_] denotes the single centered degeneracy with charge gam. OmS is supposed to be y-independent, but the y-dependence must be retained till the end of the computation";

HiggsG::usage = "HiggsG[gam_,y_] denotes the (unevaluated) stack invariant G_Higgs(gamma,y)";

Higgsg::usage = "Higgsg[gam_,y_] denotes the (unevaluated) Abelian stack invariant g_Higgs(gamma,y)";

Coulombg::usage = "Coulombg[Li_,y_] denotes the Coulomb index of n centers with charges Li";

CoulombH::usage = "CoulombH[Li_,Nvec_,y_] denotes the H-factor appearing in the formula for OmT[alpha_i] in terms of the single center degeneracies OmS[alpha_i,y]";

(** environment variables variables **)

$QuiverPerturb1::usage = "Inverse size of beta1 perturbation, default =1000";

$QuiverPerturb2::usage = "Inverse size of beta2 perturbation, default =100000";

$QuiverPrecision::usage = "Precision to decide vanishing, default=0";

$QuiverNoLoop::usage = "Default=False, set to True if quiver can be assumed to have no scaling solutions";

$QuiverTestLoop::usage = "Default=True, set to False to disable removal of CoulombH and OmS associated to non-scaling subquivers. Irrelevant if $QuiverNoLoop=True";

$QuiverVerbose::usage = "Default=True, set to False to skip data consistency tests and messages";

$QuiverMultiplier::usage = "Overall multiplier of DSZ matrix, default=1";

$QuiverDisplayCoulombH::usage = "Default=False, set to True in order that CoulombBranchFormula returns both Poincare polynomial and replacement rules for CoulombH";

(** Coulomb index computations **)

CoulombF::usage = "CoulombF[Mat_, Cvec_] returns the index of collinear solutions with DSZ products Mat, FI terms Cvec and trivial ordering.";

CoulombG::usage = "CoulombG[Mat_] returns the index of scaling collinear solutions with DSZ products Mat and trivial ordering. The total angular momentum Sum[Mat[i,j],j>i] must vanish";

CoulombIndex::usage = "CoulombIndex[Mat_,PMat_,Cvec_,y_] returns the Coulomb index for n centers with DSZ products Mat, perturbed to PMat to lift accidental degeneracies, FI terms Cvec, angular momentum fugacity y";

CoulombIndexNum::usage = "CoulombIndexNum[Mat_,PMat_,Cvec_,y_] returns the Coulomb index for n centers with DSZ products Mat, perturbed to PMat to lift accidental degeneracies,  FI terms Cvec, angular momentum fugacity y, computed numerically. Not for more than 6 centers.";

CoulombTestOrdering::usage = "CoulombTestOrdering[Mat_,Cvec_,Li_] looks numerically for collinear solutions of Coulomb problem with DSZ matrix Mat, FI terms Cvec, and ordering Li (a permutation of Range[Length[Mat]]). Not for more than 5 centers.";

CoulombFNum::usage = "CoulombFNum[Mat_,Cvec_] computes numerically the index F of collinear solutions,assuming DSZ matrix Mat and FI terms Cvec. Not for more than 5 centers.";

CoulombGNum::usage = "CoulombGNum[Mat_] computes numerically the index G of scaling collinear solutions,assuming DSZ matrix Mat. The total angular momentum Sum[Mat[i,j],j>i] must vanish. Not for more than 6 centers.";

EvalCoulombIndex::usage="EvalCoulombIndex[Mat_,PMat_,Cvec_,f_] evaluates the Coulomb indices Coulombg[{alpha_i}] appearing in g using DSZ matrix Mat, deformed to PMat, rescaled by $QuiverMultiplicity, and FI terms Cvec";

EvalCoulombIndexNum::usage="EvalCoulombIndex[Mat_,PMat_,Cvec_,f_] evaluates the Coulomb indices Coulombg[{alpha_i}] appearing in g using DSZ matrix Mat, deformed to PMat, rescaled by $QuiverMultiplicity, and FI terms Cvec, using numerical search";

(** Coulomb branch formula **)

CoulombBranchFormula::usage = "CoulombBranchFormula[Mat_,Cvec_,Nvec_,y_] expresses the Poincare polynomial of a quiver with dimension vector gam in terms of the single center degeneracies OmS[alpha_i,y] using the Coulomb branch formula, computing all CoulombH factors recursively using the minimal modification hypothesis. Also provides list of CoulombH factors if $QuiverDisplayCoulombH is set to True";

CoulombBranchFormulaFromH::usage = "CoulombBranchFormulaFromH[Mat_,Cvec_,Nvec_,R_,y_] expresses the Poincare polynomial of a quiver with dimension vector gam in terms of the single center degeneracies OmS[alpha_i,y] using the Coulomb branch formula, using CoulombH factors provided in replacement rule R";

QuiverPoincarePolynomial::usage = "QuiverPoincarePolynomial[gam_,y_] expresses the Poincare polynomial of a quiver with dimension vector gam in terms of the total single center degeneracies OmT[alpha_i,y] and Coulomb indices Coulombg[{alpha_i},y]. If gam is primitive, QuiverPoincarePolynomial[gam] coincides with QuiverPoincarePolynomialRat[gam_].";

QuiverPoincarePolynomialRat::usage = "QuiverPoincarePolynomialRat[gam_,y_] expresses the rational Poincare polynomial of a quiver with dimension vector gam in terms of the total single center degeneracies OmT[alpha_i,y] and Coulomb indices Coulombg[{alpha_i},y]";

QuiverPoincarePolynomialExpand::usage ="QuiverPoincarePolynomialExpand[Mat_,PMat_,Cvec_,Nvec_,Q_]evaluates the Coulomb indices Coulombg[{alpha_i}] and expresses the total single center degeneracies OmT[alpha_i,y] in terms of the single center degeneracies OmS[alpha_i,y] and the CoulombH factors inside the Poincare polynomial Q";

ListCoulombH::usage = "ListCoulombH[Nvec_,Q_] returns a pair {ListH,ListC} where ListH is a list of CoulombH factors possibly appearing in the Poincare polynomial Q of a quiver with dimension vector  Nvec, and ListC is the list of coefficients which multiply the monomials in OmS[alpha_i,y] canonically associated to the CoulombH factors in Q. ";

SolveCoulombH::usage = "SolveCoulombH[ListH_,ListC_,soH_] returns a list of replacement rules for the CoulombH factors in ListH, applying the minimal modification hypothesis to the corresponding coefficient in ListC. The last argument soH is a replacement rule for CoulombH factors associated to subquivers. ";

(** Higgs branch formula **)

HiggsBranchFormula::usage = "HiggsBranchFormula[Mat_,Cvec_,Nvec_,y_] computes the Poincare polynomial of a quiver with DSZ matrix Mat, FI parameters Cvec, dimension vector Nvec using Reineke's formula. Accurate only for quivers without closed loops.";

StackInvariant::usage = "StackInvariant[Mat_,Cvec_,Nvec_,y_] gives the stack invariant of a quiver with DSZ matrix Mat, dimension vector Nvec and FI parameters Cvec computed using Reineke's formula";

AbelianStackInvariant::usage = "AbelianStackInvariant[Mat_,Cvec_,y_] gives the Abelian stack invariant of a quiver with DSZ matrix Mat and FI parameters Cvec computed using Reineke's formula";

QFact::usage = "QFact[Nvec_,y_] represents the unevaluated q-deformed Factorial";

QDeformedFactorial::usage = "QDeformedFactorial[n_,y_] gives the q-deformed factorial";

EvalQFact::usage = "EvalQFact[f_] replaces QFact[n_,y_] with QDeformedFactorial[n,y] everywhere in f";


(** Utilities **)

SymmetryFactor::usage = "SymmetryFactor[pa_] gives 1/|Aut| where Aut is the subgroup of the permutation group leaving the list pa invariant";

OmTRat::usage = "OmTRat[gam_,y_] gives the rational total invariant. Coincides with OmT[gam_,y_] if gam is primitive";

ListAllPartitions::usage = "ListAllPartitions[gam_] returns the list of unordered partitions of the positive integer vector gam as a sum of positive integer vectors"; 

ListAllPartitionsMult::usage = "ListAllPartitionsMult[gam_] returns the list of unordered partitions of the positive integer vector gam as a sum of positive integer vectors with multiplicities"; 

ListSubQuivers::usage = "ListSubQuivers[Nvec_] gives a list of all dimension vectors less or equal to Nvec";

SimplifyOmSbasis::usage = "SimplifyOmSbasis[f_] replaces OmS[gam,y]->1 when gam is a basis vector";

SimplifyOmSmultbasis::usage = "SimplifyOmSmultbasis[f_] replaces OmS[gam,y]->0 if gam is a non-trivial multiple of a basis vector";

DropFugacity::usage = "DropFugacity[f_] replaces OmS[gam,y]->OmS[gam] in f";

EvalCoulombH3::usage = "EvalCoulombH3[Mat_,f_] evaluates any 3-center CoulombH factor in f.";

TestNoLoop::usage = "TestNoLoop[Mat_,Li_] tests if the quiver made from vectors in list Li is a tree";

TestNoFullLoop::usage = "TestNoFullLoop[Mat_,Li_] tests if the quiver made from vectors in list Li has no loop going through all nodes";

CoulombHNoLoopToZero::usage = "CoulombHNoLoopToZero[Mat_,f_] sets to zero any CoulombH factor in f corresponding to non-scaling subquivers. Returns f is $QuiverTestLoop=False.";

OmTNoLoopToZero::usage = "OmTNoLoopToZero[Mat_,f_]sets to zero any OmT in f corresponding to non-scaling subquivers (except basis vectors). Returns f is $QuiverTestLoop=False.";

OmSNoLoopToZero::usage = "OmSNoLoopToZero[Mat_,f_]sets to zero any OmS in f corresponding to non-scaling subquivers (except basis vectors). Returns f is $QuiverTestLoop=False.";

OmTToOmS::usage="OmTToOmS[f_] expands any OmT in f into sums of products of CoulombH and OmS factors";

SubDSZ::usage = "SubDSZ[Mat_,Li_] gives the DSZ matrix of the subquiver made of vectors in list Li";

MinimalModif::usage = "MinimalModif[f_] returns the symmetric Laurent polynomial which coincides with the Laurent expansion expansion of the symmetric rational function f at y=0, up to strictly positive powers of y. Here symmetric means invariant under y->1/y.";

OmToOmb::usage = "OmToOmb[f_] expresses any Om[gam,y] in f in terms of Omb[gam,y]";

OmbToOm::usage = "OmbToOm[f_] expresses any Omb[gam,y] in f in terms of Om[gam,y]";

StackInvariantToOmb::usage = "StackInvariantToOmb[gam_,y_] expresses the stack invariant GHiggs[gam,y] in terms of sums of products of Omb; Coincides with Omb[gam,y] if charge vector is primitive";

HiggsGToOmb::usage = "HiggsGToOmb[f_] expresses any HiggsG[gam,y] in f in terms of Omb[gam,y]";

OmbToHiggsG::usage = "OmbToHiggsG[f_] expresses any Omb[gam,y] in f in terms of HiggsG[gam,y]";

EvalHiggsg::usage = "EvalHiggsg[Mat_,Cvec_,f_] evaluates any Higgsg[Li,y] appearing in f using Reineke's formula for Abelian quivers";

EvalHiggsG::usage = "EvalgHiggsG[Mat_,Cvec_,f_] evaluates any HiggsG[gam,y] appearing in f using Reineke's formula";

CoulombHSubQuivers::usage = "CoulombHSubQuivers[Mat_,PMat_,Nvec_,y_] computes all CoulombH factors for dimension vector strictly less than Nvec";

RandomCvec::usage = "RandomCvec[gam_] generates a random set of FI parameters between -1 and 1";

UnitStepWarn::usage = "UnitStepWarn[x_] gives 1 for x>0, 0 for x<0, and produces a warning for x=0";

Mutate::usage = "Mutate[{Mat_,Cvec_,Nvec_},klist_] mutates the quiver with respect to nodes in klist";

QuiverPlot::usage = "QuiverPlot[Mat_] displays the quiver with DSZ matrix Mat";


Begin["`Private`"]


(* ::Section:: *)
(*Recursive formulae for the n-center Coulomb index *)


$QuiverPerturb1=1000;
$QuiverPerturb2=10^10; 
$QuiverPrecision=0;
$QuiverNoLoop=False;
$QuiverTestLoop=True;
$QuiverVerbose=True;
$QuiverMultiplier=1;
$QuiverDisplayCoulombH=False;

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

UnitStepWarn[x_]:=Which[x>0,1,x<0,0,x==0,Print["UnitStepWarn: argument vanishes, returns 1/2"];1/2]; 

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
	RMat=Table[Random[Integer,{1,1000}],{i,m},{j,m}];
	RMat=1/1000/$QuiverPerturb2 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,m},{j,m}];
	RCvec=1/1000/$QuiverPerturb2 Table[Random[Integer,{1,1000}],{i,m}];
	RCvec[[m]]=-Sum[RCvec[[i]],{i,m-1}];
	(y-1/y)^(1-m) (-1)^(Sum[$QuiverMultiplier Mat[[i,j]],{i,Length[Cvec]},{j,i+1,m}]+m-1)
	   Sum[y^($QuiverMultiplier Sum[Mat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,i+1,m}])
		CoulombF[Table[PMat[[ListPerm[[k,i]],ListPerm[[k,j]]]]+
					   RMat[[ListPerm[[k,i]],ListPerm[[k,j]]]],{i,m},{j,m}],
                 Table[Cvec[[ListPerm[[k,i]]]]+RCvec[[ListPerm[[k,i]]]],{i,m}]],
       {k,Length[ListPerm]}]
];

(* induction rule for F *)
CoulombF[Mat_,Cvec_]:=Module[{m=Length[Mat]},
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
]];

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




(* ::Section:: *)
(*Numerical evaluation of the n-center Coulomb index *)


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
	ListPerm=Permutations[Range[m]];
    Do[ If[Abs[Sum[Cvec[[ListPerm[[j,i]]]],{i,k}]]<=$QuiverPrecision, 
           If[Abs[Sum[Mat[[ListPerm[[j,i1]],ListPerm[[j,i2]]]],
                {i1,k},{i2,k+1,m}]]>$QuiverPrecision,
               Print["CoulombIndex: FI sit on wall of marginal stability"];Break[]];
          ],{k,1,IntegerPart[m/2]},{j,Length[ListPerm]}
    ];	
    CoulombOrderings=Select[Table[
	CoulombHessian=Table[If[i==j,(PMat[[1,i]]+RMat[[1,i]]) z[i]/Abs[z[i]]^3+Sum[If[i==k,0,(PMat[[i,k]]+RMat[[i,k]])(z[k]-z[i])/Abs[z[k]-z[i]]^3],{k,2,Length[Cvec]}],-(PMat[[i,j]]+RMat[[i,j]])(z[j]-z[i])/Abs[z[j]-z[i]]^3],{i,2,m},{j,2,m}];
	Eq=Flatten[{Table[Sum[If[i==j,0,
      (PMat[[ListPerm[[pa,i]],ListPerm[[pa,j]]]]+RMat[[ListPerm[[pa,i]],ListPerm[[pa,j]]]])
      /(z[ListPerm[[pa,j]]]-z[ListPerm[[pa,i]]])Sign[j-i]],{j,Length[Cvec]}]
      -Cvec[[ListPerm[[pa,i]]]]-RCvec[[ListPerm[[pa,i]]]],{i,m}]==0,z[1]==0}];
	soN=NSolve[Eq,Table[z[i],{i,m}]];
	Listimsol=Table[Chop[Im[Table[z[i],{i,m}]/.soN[[j]]]],{j,Length[soN]}];
	Listrealsol=Flatten[Position[Listimsol,Table[0,{i,m}]]];
	Listord=Table[Table[z[ListPerm[[pa,i]]]<=z[ListPerm[[pa,i+1]]],{i,m-1}]/.{z[i_]->Re[z[i]]}/.soN[[Listrealsol[[j]]]],{j,Length[Listrealsol]}];
	Listcorrectord=Flatten[Position[Listord,Table[True,{i,m-1}]]];
	If[Length[Listcorrectord]>1,Print["CoulombIndexNum:More than 1 solution:",Length[Listcorrectord],ListPerm[[pa]]]];
	If[Length[Listcorrectord]>0,
	  {ListPerm[[pa]],
		Sum[Mat[[ListPerm[[pa,i]],ListPerm[[pa,j]]]],{i,m},{j,i+1,m}],
		Sum[Sign[Det[(CoulombHessian/.{z[i_]->Re[z[i]]}/.
			soN[[Listrealsol[[Listcorrectord[[j]]]]]])]],{j,Length[Listcorrectord]}]}]
		,{pa,1,Length[ListPerm]}],Length[#]>0&];
	Simplify[(-1)^(Sum[$QuiverMultiplier Mat[[i,j]],{i,m},{j,i+1,m}]+m-1)
		Sum[CoulombOrderings[[i,3]]y^($QuiverMultiplier CoulombOrderings[[i,2]]),{
	i,Length[CoulombOrderings]}]/(y-1/y)^(m-1)]];

(* evaluate Coulombg numerically *)
EvalCoulombIndexNum[Mat_,PMat_,Cvec_,f_]:=f/.{Coulombg[Li_,y_]:>CoulombIndexNum[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]};



(* ::Section:: *)
(*Coulomb branch formula for quiver invariants*)


CoulombBranchFormula[Mat_,Cvec_,Nvec_,y_]:=Module[{RMat,QPoinca,ListH,ListCoef,soMinimalModif,soH},
  If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
      Print["CoulombBranchFormula: Length of DSZ matrices, FI and dimension vectors do not match !"]];
  If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["CoulombBranchFormula: DSZ matrix is not antisymmetric !"]];
  If[Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision,
		Print["CoulombBranchFormula: FI terms do not sum up to zero !"]];
  RMat=Table[Random[Integer,{1,1000}],{i,Length[Mat]},{j,Length[Mat]}];
  RMat=1/1000/$QuiverPerturb1 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,Length[Mat]},{j,Length[Mat]}];
  Print["CoulombBranchFormula: Constructing Poincar\[EAcute] polynomial..."]; 
  QPoinca=SimplifyOmSmultbasis[
	QuiverPoincarePolynomialExpand[Mat,Mat+RMat,Cvec,Nvec,QuiverPoincarePolynomial[Nvec,y]]];
  If[$QuiverNoLoop,
    If[$QuiverDisplayCoulombH,
       {DropFugacity[SimplifyOmSbasis[QPoinca/.{CoulombH[x__]:>0}]],{}},
       DropFugacity[SimplifyOmSbasis[QPoinca/.{CoulombH[x__]:>0}]]
    ]   
  ,
  (*else *)  
     Module[{},
       soH=CoulombHSubQuivers[Mat,Mat+RMat,Nvec,y];
       {ListH,ListCoef}=ListCoulombH[Nvec,QPoinca];       
       If[Length[ListH]==0,
		soMinimalModif={},
        soMinimalModif=Simplify[SolveCoulombH[ListH,ListCoef,soH],
             $QuiverMultiplier\[Element]Integers]]
     ];
     Print["CoulombBranchFormula: Substituting CoulombH factors..."]; 
     If[$QuiverDisplayCoulombH,
       {DropFugacity[SimplifyOmSbasis[QPoinca/.soMinimalModif/.soH]],Union[Flatten[{soH,soMinimalModif}]]/.y$->y},
        DropFugacity[SimplifyOmSbasis[QPoinca/.soMinimalModif/.soH]]
     ]
  ]
];

CoulombBranchFormulaFromH[Mat_,Cvec_,Nvec_,soH_,y_]:=Module[{RMat,QPoinca},
  If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
      Print["CoulombBranchFormulaFromH: Length of DSZ matrices, FI and dimension vectors do not match !"]];
  If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["CoulombBranchFormulaFromH: DSZ matrix is not antisymmetric !"]];
  If[Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision,
		Print["CoulombBranchFormulaFromH: FI terms do not sum up to zero !"]];
  RMat=Table[Random[Integer,{1,1000}],{i,Length[Mat]},{j,Length[Mat]}];
  RMat=1/1000/$QuiverPerturb1 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,Length[Mat]},{j,Length[Mat]}];
  Print["CoulombBranchFormulaFromH: Constructing Poincar\[EAcute] polynomial..."]; 
  QPoinca=SimplifyOmSmultbasis[
	QuiverPoincarePolynomialExpand[Mat,Mat+RMat,Cvec,Nvec,QuiverPoincarePolynomial[Nvec,y]]];
  If[$QuiverNoLoop,
       DropFugacity[SimplifyOmSbasis[QPoinca/.{CoulombH[x__]:>0}]]       
  , (*else *)  
     Module[{},
       Print["CoulombBranchFormulaFromH: Substituting your CoulombH factors..."]; 
       DropFugacity[SimplifyOmSbasis[QPoinca/.soH]]
     ]
  ]
];

(* step by step *)

QuiverPoincarePolynomialRat[gam_,y_]:=Module[{ListAllPart},
	ListAllPart=ListAllPartitions[gam];
    Sum[Coulombg[ListAllPart[[i]],y]SymmetryFactor[ListAllPart[[i]]]
		Product[OmTRat[ListAllPart[[i,j]],y],{j,Length[ListAllPart[[i]]]}],{i,Length[ListAllPart]}]];

QuiverPoincarePolynomial[gam_,y_]:=DivisorSum[GCD@@gam,
	MoebiusMu[#]/# (y-1/y)/(y^#-y^(-#)) QuiverPoincarePolynomialRat[gam/#,y^#]&];

(* evaluate Coulombg using induction rule *)
EvalCoulombIndex[Mat_,PMat_,Cvec_,f_]:=f/.{Coulombg[Li_,y_]:>CoulombIndex[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]]Li[[j,l]]PMat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]};

QuiverPoincarePolynomialExpand[Mat_,PMat_,Cvec_,Nvec_,QPoinca_]:=OmSNoLoopToZero[PMat,
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
         Print["Evaluating CoulombH factors for dimension vector ",LiLevel[[i]]];
        QPoinca=SimplifyOmSmultbasis[QuiverPoincarePolynomialExpand[Mat,PMat,
                RandomCvec[LiLevel[[i]]],LiLevel[[i]],QuiverPoincarePolynomial[LiLevel[[i]],y]]];
	     {ListH,ListCoef}=ListCoulombH[LiLevel[[i]],QPoinca];
         If[Length[ListH]==0,
	      soMinimalModif={},    
          soMinimalModif=Simplify[SolveCoulombH[ListH,ListCoef,ListCoulombHLevel],$QuiverMultiplier\[Element]Integers];
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


(* utilities *)

SymmetryFactor[pa_]:=Length[Permutations[pa]]/Length[pa]!;

OmTRat[gam_,y_]:=DivisorSum[GCD@@gam,(y-1/y)/#/(y^#-1/y^#)OmT[gam/#,y^#]&];

SimplifyOmSbasis[f_]:=f/.{OmS[gam_,y_]:>1/; (Plus@@gam==1)};

SimplifyOmSmultbasis[f_]:=f/.{OmS[gam_,y_]:>0/; (Plus@@gam>1)&& 
          (Union[gam]=={0,Plus@@gam})};

DropFugacity[f_]:=f/. {OmS[gam_,y_]:>OmS[gam]};

TestNoLoop[Mat_,Li_]:=Module[{m,MatProd,ListPerm},
	m=Length[Li];
    Which[
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
      OmS[gam_,y_]:>0 /;TestNoFullLoop[Mat,
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

SubDSZ[Mat_,Li_]:=
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}];

OmToOmb[f_]:=f/. {Om[gam_,y_]:>DivisorSum[GCD@@gam,(y-1/y)/(y^#-1/y^#)/# MoebiusMu[#] Omb[gam/#,y^#]&]};

OmbToOm[f_]:=f/. {Omb[gam_,y_]:>DivisorSum[GCD@@gam,(y-1/y)/(y^#-1/y^#)/# Om[gam/#,y^#]&]};

ListSubQuivers[Nvec_]:=Module[{k},Flatten[Table[k/@Range[Length[Nvec]],##]&@@({k[#],0,Nvec[[#]]}&/@Range[Length[Nvec]]),
	Length[Nvec]-1]];

ListAllPartitions[gam_]:=Module[{m,unit,Li},
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
]

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



RandomCvec[gam_]:=Module[{m,mnonzero,k,Cvec},
	m=Length[gam];
	mnonzero=Select[Range[m],gam[[#]]>0&];
      If[Length[mnonzero]==0,Cvec=0 Range[m],
        k=Last[mnonzero];
        Cvec=Table[Random[Integer,{-1000,1000}],{i,m}];
        Cvec[[k]]=-Sum[If[i==k,0,gam[[i]]Cvec[[i]]],{i,m}]/gam[[k]];
	];
	Cvec/$QuiverPerturb1
];


(* ::Section:: *)
(*Reineke's formula for stack invariants*)


HiggsBranchFormula[Mat_,Cvec_,Nvec_,y_]:=Module[{},
  If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
      Print["HiggsBranchFormula: Length of DSZ matrices, FI and dimension vectors do not match !"]];
  If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["HiggsBranchFormula: DSZ matrix is not antisymmetric !"]];
  If[Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision,
		Print["HiggsBranchFormula: FI terms do not sum up to zero !"]];
 EvalQFact[EvalHiggsG[Mat,Cvec,OmbToHiggsG[OmToOmb[Om[Nvec,y]]]]]
];

StackInvariant[Mat_,Cvec_,Nvec_,y_]:=Module[{m,ListAllPermutations,pa},
  m=Length[Nvec];
  pa=Flatten[Map[Permutations,ListAllPartitions[Nvec]],1];
  If[$QuiverVerbose,
    If[Length[Union[{Length[Cvec],Length[Mat],Length[Nvec]}]]>1, 
        Print["StackInvariant: Length of DSZ matrix, FI and dimension vectors do not match !"]];
    If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["StackInvariant: DSZ matrix is not antisymmetric !"]];
    If[Abs[Plus@@(Nvec Cvec)]>$QuiverPrecision,
		Print["StackInvariant: FI parameters do not sum up to 0 !"]];
    Print["StackInvariant: summing ", Length[pa]," ordered partitions"];
  ];
  (-y)^($QuiverMultiplier Sum[-Max[Mat[[k,l]],0]Nvec[[k]]Nvec[[l]],{k,m},{l,m}]-1+Plus@@ Nvec)
	   (y^2-1)^(1-Plus@@Nvec)
	Sum[If[(Length[pa[[i]]]==1) ||And@@Table[Sum[Cvec[[k]] pa[[i,a,k]],{a,b},{k,m}]>0,{b,Length[pa[[i]]]-1}],
      (-1)^(Length[pa[[i]]]-1)
       y^(2$QuiverMultiplier  Sum[Max[Mat[[l,k]],0] pa[[i,a,k]]pa[[i,b,l]],
    {a,1,Length[pa[[i]]]},{b,a,Length[pa[[i]]]},{k,m},{l,m}])/
    Product[QFact[pa[[i,j,k]],y] ,{j,1,Length[pa[[i]]]},{k,m}],0],{i,Length[pa]}]
];

AbelianStackInvariant[Mat_,Cvec_,y_]:=Module[{m,ListAllPermutations,pa,ListPerm},
  m=Length[Cvec];
  pa=Flatten[Map[Permutations,ListAllPartitions[ConstantArray[1,m]]],1];
  If[$QuiverVerbose,
    If[Length[Union[{Length[Cvec],Length[Mat]}]]>1, 
        Print["AbelianStackInvariant: Length of DSZ matrix and FI  vectors do not match !"]];
    If[Max[Abs[Flatten[Mat+Transpose[Mat]]]]>$QuiverPrecision,
		Print["AbelianStackInvariant: DSZ matrix is not antisymmetric !"]];
    If[Abs[Plus@@Cvec]>$QuiverPrecision,
		Print["AbelianStackInvariant: FI parameters do not sum up to 0 !"]]; 
    ListPerm=Permutations[Range[m]];
    Do[ If[Abs[Sum[Cvec[[ListPerm[[j,i]]]],{i,k}]]<=$QuiverPrecision, 
           If[Abs[Sum[Mat[[ListPerm[[j,i1]],ListPerm[[j,i2]]]],
                {i1,k},{i2,k+1,m}]]>$QuiverPrecision,
               Print["AbelianStackInvariant: FI sit on wall of marginal stability"];
               Break[],
			   Print["AbelianStackInvariant: FI sit on wall of threshold stability"];
               Break[]
             ];
          ],{k,1,IntegerPart[m/2]},{j,Length[ListPerm]}
    ];
    Print["AbelianStackInvariant: summing ", Length[pa]," ordered partitions"];
  ];	
  (-y)^($QuiverMultiplier Sum[-Max[Mat[[k,l]],0],{k,m},{l,m}]-1+m)
	   (y^2-1)^(1-m)
	Sum[If[(Length[pa[[i]]]==1) ||And@@Table[Sum[Cvec[[k]] pa[[i,a,k]],{a,b},{k,m}]>0,
          {b,Length[pa[[i]]]-1}],
      (-1)^(Length[pa[[i]]]-1)
       y^(2$QuiverMultiplier  Sum[Max[Mat[[l,k]],0] pa[[i,a,k]]pa[[i,b,l]],
    {a,1,Length[pa[[i]]]},{b,a,Length[pa[[i]]]},{k,m},{l,m}])/
    Product[QFact[pa[[i,j,k]],y] ,{j,1,Length[pa[[i]]]},{k,m}],0],{i,Length[pa]}]
];

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

EvalHiggsG[Mat_,Cvec_,f_]:=f/.{HiggsG[gam_,y_]:>StackInvariant[Mat,Cvec,gam,y]};

EvalHiggsg[Mat_,Cvec_,f_]:=f/.{Higgsg[Li_,y_]:>AbelianStackInvariant[
	Table[Sum[Li[[i,k]]Li[[j,l]]Mat[[k,l]],{k,Length[Mat]},{l,Length[Mat]}],
      {i,Length[Li]},{j,Length[Li]}],
	Table[Sum[Li[[i,k]] Cvec[[k]],{k,Length[Mat]}],{i,Length[Li]}],y]};


(*Mutate[{Mat_,Cvec_,Nvec_},k_]:=Module[{m},
  m=Length[Mat];
  {Table[If[(i==k)||(j==k),-Mat[[i,j]],Mat[[i,j]]+Max[0,Mat[[i,k]] Mat[[k,j]]] Sign[Mat[[k,j]]]],{i,m},{j,m}],
   Table[If[i==k,-Cvec[[i]],Cvec[[i]]+Max[0,Mat[[i,k]]] Cvec[[k]]],{i,m}],
   Table[If[i==k,-Nvec[[i]]+Sum[Nvec[[j]] Max[0,Mat[[j,k]]],{j,m}],Nvec[[i]]],{i,m}]}];
*)

Mutate[{Mat_,Cvec_,Nvec_},klist_]:=Module[{m,Mat2,Cvec2,Nvec2,k},
  If[Length[klist]>1,
    {Mat2,Cvec2,Nvec2}=Mutate[{Mat,Cvec,Nvec},Drop[klist,-1]]; 
       k=Last[klist];,
    {Mat2,Cvec2,Nvec2}={Mat,Cvec,Nvec};
       k=klist[[1]];
  ];
  m=Length[Mat2];
  {Table[If[(i==k)||(j==k),-Mat2[[i,j]],Mat2[[i,j]]+Max[0,Mat2[[i,k]] Mat2[[k,j]]] Sign[Mat2[[k,j]]]],{i,m},{j,m}],
   Table[If[i==k,-Cvec2[[i]],Cvec2[[i]]+Max[0,Mat2[[i,k]]] Cvec2[[k]]],{i,m}],
   Table[If[i==k,-Nvec2[[i]]+Sum[Nvec2[[j]] Max[0,Mat2[[j,k]]],{j,m}],Nvec2[[i]]],{i,m}]}];

QuiverPlot[Mat_]:=GraphPlot[Table[Max[Mat[[i,j]],0],{i,Length[Mat]},{j,Length[Mat]}],
      DirectedEdges->True,MultiedgeStyle->True,VertexLabeling->True];


(* ::Text:: *)
(**)


End[];
EndPackage[]
