(* ::Package:: *)

(* CoulombHiggsFast: faster flow tree formula for quivers with general dimension vectors.
   Load AFTER CoulombHiggs.m.  Uses the symbols y, OmAtt, OmAttb of CoulombHiggs`.

   Main entry points:
     FastFlowTreeFormula[Mat, Cvec, Nvec]            -- same output convention as FlowTreeFormula
     FastFlowTreeFormulaRat[Mat, Cvec, Nvec]         -- rational index, in terms of OmAttb
     FastFlowTreeFormula[Mat, Cvec, Nvec, OmStar]    -- OmStar[gam, y] gives integer attractor indices
                                                       (e.g. 1 for basis vectors, 0 otherwise)
   Algorithm: recursion at the level of charges (not of individual centers).
   Along the straight attractor flow c(l) = c + l c*_gam, (c*_gam . a = <gam,a>), the walls crossed
   are grouped by their position l_w; all splittings on a given wall lie in a rank-2 sublattice
   Lambda (checked).  The jump across the wall is given by the Kontsevich-Soibelman formula in the
   quantum torus of Lambda (truncated to charges <= gam), with the indices of all charges in
   Lambda evaluated just after the wall (recursively, by their own flow).  Exact infinitesimal
   displacements (lexicographic lists of FI vectors) replace the random perturbations of the
   original code, so the result is deterministic.

   Coulomb branch formula: loading this file sets $QuiverCoulombOpt = 2, so that EvalCoulombIndex
   (used by CoulombBranchFormula) evaluates all Coulomb indices with >= 5 centres by the compiled
   program c/coulombph (C++, closed formula with exact sign tests), or c/coulombidx (a translation of
   CoulombFOpt/CoulombGOpt) when $QuiverNoLoop is True, with fallback to CoulombIndexOpt;
   TestNoLoop is replaced by an equivalent acyclicity test.
   Build: c++ -O3 -std=c++17 -o c/coulombph c/coulombph.cpp -lpthread  (same for coulombidx).
   Set $QuiverCoulombOpt = 1 to recover the original behaviour. *)

BeginPackage["CoulombHiggsFast`", {"CoulombHiggs`", "IndexVars`"}];

FastFlowTreeFormula::usage = "FastFlowTreeFormula[Mat,Cvec,Nvec] or FastFlowTreeFormula[Mat,Cvec,Nvec,OmStar] computes the index with the flow tree formula, in terms of OmAtt[gam,y] (or of the integer attractor indices OmStar[gam,y]).";
FastFlowTreeFormulaRat::usage = "FastFlowTreeFormulaRat[Mat,Cvec,Nvec] or FastFlowTreeFormulaRat[Mat,Cvec,Nvec,OmStar] computes the rational index with the flow tree formula, in terms of OmAttb[gam,y] (or of OmStar).";
FastCoulombIndex::usage = "FastCoulombIndex[Mat,PMat,Cvec,y] is CoulombIndexOpt with memoization of the F and G recursions.";
CCoulombIndex::usage = "CCoulombIndex[Mat,PMat,Cvec,y] computes the same Coulomb index as CoulombIndexOpt, using the compiled program $CoulombIdxExe (c/coulombph, exact sign tests; c/coulombidx when $QuiverNoLoop is True), with fallback to the exact Mathematica routine when a sign test is ambiguous.";
CCoulombIndexPerturbed::usage = "CCoulombIndexPerturbed[Mat,PMatPert,CvecPert,y] runs the compiled program on already perturbed data.";
$CoulombIdxExe::usage = "path to the compiled Coulomb index program (default: c/coulombph, closed formula, in the directory of CoulombHiggsFast.m); set it after loading the add-on if the program is elsewhere. If the file does not exist, Coulomb indices are computed in Mathematica.";
$CoulombIdxRecExe::usage = "path to the compiled program c/coulombidx (translation of the recursion of CoulombFOpt, CoulombGOpt), used instead of $CoulombIdxExe when $QuiverNoLoop is True";
$CoulombIdxThreads::usage = "number of threads used by the compiled Coulomb index programs (default 8)";
$FastPerturbRange::usage = "number of values from which the random perturbations of the fast Coulomb branch formula are drawn (default 10^5; the original code uses 1000)";
$CoulombIdxDoubleDouble::usage = "number of Coulomb indices that the compiled program had to redo in double-double arithmetic";
$CoulombIdxFallbacks::usage = "number of Coulomb indices for which the compiled program detected a sign test within roundoff and the exact Mathematica routine was used instead";
KSWallCrossingRat::usage = "KSWallCrossingRat[Mat, Omb1, c1, c2, Nvec] applies the Kontsevich-Soibelman wall-crossing formula for a quiver with antisymmetrized exchange matrix Mat: given the rational indices Omb1 of all dimension vectors 0<alpha<=Nvec at stability (FI) parameter c1 (Omb1 is an Association alpha->value or a function Omb1[alpha]; values are rational functions of y, possibly symbolic), it returns the Association alpha -> rational index at stability parameter c2, for all 0<alpha<=Nvec. c1, c2 are FI vectors (slope of alpha = c.alpha/Total[alpha]); a list of FI vectors {c0,c1,...} stands for c0+eps c1+eps^2 c2+... with eps infinitesimal. Option \"CollectPattern\" (default _OmAttb|_OmAtt|_Omb|_Om|_OmS|_OmT) gives the symbols on which coefficients are collected.";
KSWallCrossing::usage = "KSWallCrossing[Mat, Om1, c1, c2, Nvec] is the same as KSWallCrossingRat for integer (refined) indices: Om1 is a function Om1[alpha, y] or an Association alpha->Omega(alpha,y) of the integer indices at c1; returns the Association alpha -> integer index at c2. Rational and integer indices are related by Omb(alpha,y)=Sum_{d|alpha} (y-1/y)/(d (y^d-y^-d)) Om(alpha/d, y^d).";
FastFlowTreeClear::usage = "FastFlowTreeClear[] clears the memoization tables of FastFlowTreeFormula and FastFlowTreeFormulaRat.";
FastFlowTreeStats::usage = "FastFlowTreeStats[] gives {number of memoized states, number of walls processed} in the fast flow tree routines.";
FastCoulombBranchFormula::usage = "FastCoulombBranchFormula[Mat,Cvec,Nvec] computes the same quantity as CoulombBranchFormula[Mat,Cvec,Nvec], with sparse polynomials instead of global replacements on one large expression. Loading CoulombHiggsFast.m makes CoulombBranchFormula call it when $QuiverCoulombOpt==2 (set by loading the add-on; $QuiverCoulombOpt=1 restores the original code).";

Begin["`Private`"];

(* ---------- lexicographic infinitesimals ---------- *)
lexSign[l_List] := Module[{p = SelectFirst[l, # =!= 0 &, 0]}, Sign[p]];
lexLess[a_List, b_List] := lexSign[PadRight[b, Max[Length[a], Length[b]]] - PadRight[a, Max[Length[a], Length[b]]]] > 0;

(* normalize c (list of FI vectors) for dimension vector gam: c.gam = 0 at each order *)
normalizeC[c_List, gam_List] := Module[{tot = Total[gam]}, Map[# - (# . gam)/tot &, c]];

(* sub-dimension vectors 0 < d < gam *)
subVecs[gam_List] := Rest[Most[Tuples[Range[0, #] & /@ gam]]];

(* rational attractor index from integer one *)
omStarBar[OmStar_, gam_List, yy_] := DivisorSum[GCD @@ gam,
   (yy - 1/yy)/(# (yy^# - yy^(-#))) (OmStar[gam/#, yy^#]) &];

(* ---------- truncated quantum torus product on a rank-2 sublattice ---------- *)
(* elements: Association charge -> coefficient ; x^a x^b = (-y)^<a,b> x^(a+b) *)
qtMul[f_Association, g_Association, Mat_, gam_] := Module[{res = <||>, s, k},
  KeyValueMap[Function[{a, ca},
     KeyValueMap[Function[{b, cb},
        s = a + b;
        If[And @@ Thread[s <= gam],
         k = a . Mat . b;
         res[s] = Lookup[res, Key[s], 0] + (-y)^k ca cb]], g]], f];
  res];

qtExp[f_Association, Mat_, gam_] := Module[{res = <|0 gam -> 1|>, term = <|0 gam -> 1|>, n = 0},
  While[Length[term] > 0,
   n++;
   term = DeleteCases[Map[simp, qtMul[term, f, Mat, gam]/n], 0];
   res = Merge[{res, term}, Total];];
  res];

(* coefficients are collected on the symbols matching $ksPattern, with Together on each coefficient *)
$ksPattern = _OmAttb;
simp[e_] := If[FreeQ[e, $ksPattern], Together[e], Collect[Expand[e], $ksPattern, Together]];

(* product of exponentials exp(sum_{a in ray} om[a] x^a/(y-1/y)) over rays in the given order *)
qtProduct[rays_List, om_Association, Mat_, gam_] := Module[{res = <|0 gam -> 1|>},
  Do[res = DeleteCases[Map[simp,
       qtMul[res, qtExp[Association[Map[# -> om[#]/(y - 1/y) &, ray]], Mat, gam], Mat, gam]], 0],
   {ray, rays}];
  res];

(* log of an element supported on a single ray (commutative), without constant term 1 *)
rayLog[f_Association, gam_] := Module[{g = KeyDrop[f, Key[0 gam]], res = <||>, term, n = 0},
  term = <|0 gam -> 1|>;
  While[True, n++;
   term = DeleteCases[Map[simp, rayMul[term, g, gam]], 0];
   If[Length[term] == 0, Break[]];
   res = Merge[{res, (-1)^(n + 1) term/n}, Total]];
  res];
rayMul[f_, g_, gam_] := Module[{res = <||>, s},
  KeyValueMap[Function[{a, ca}, KeyValueMap[Function[{b, cb}, s = a + b;
       If[And @@ Thread[s <= gam], res[s] = Lookup[res, Key[s], 0] + ca cb]], g]], f]; res];

(* given P = prod over rays (decreasing slope at c+) of exp(sum om[a] x^a/(y-1/y)), return om[gam] *)
peel[P0_Association, rays_List, gam_, Mat_] := Module[{P = P0, R, ray},
  Do[
   R = rayLog[KeySelect[P, MemberQ[ray, #] || # == 0 gam &], gam];
   If[MemberQ[ray, gam], Return[simp[Lookup[R, Key[gam], 0] (y - 1/y)], Module]];
   If[Length[R] > 0, P = DeleteCases[Map[simp, qtMul[qtExp[-R, Mat, gam], P, Mat, gam]], 0]],
   {ray, rays}]];

(* order charges in rays by decreasing slope c.a/|a| (c lexicographic) *)
raysByDecreasingSlope[charges_List, c_List] := Module[{sl, groups},
  sl = Map[{#, Map[Function[cc, cc . #/Total[#]], c]} &, charges];
  groups = GatherBy[sl, Last];
  groups = Sort[groups, lexLess[#2[[1, 2]], #1[[1, 2]]] &];
  Map[Map[First, #] &, groups]];

(* ---------- standalone Kontsevich-Soibelman wall-crossing ---------- *)
Options[KSWallCrossingRat] = {"CollectPattern" -> (_OmAttb | _OmAtt | _Omb | _Om | _OmS | _OmT)};
Options[KSWallCrossing] = Options[KSWallCrossingRat];
KSWallCrossingRat::ray = "Non-collinear charges `1` have the same slope at the stability parameter `2`: it lies on a wall. Perturb it, or give a list {c, dc} for c + eps dc.";

toLex[c_] := If[MatrixQ[c], c, {c}];

(* factorize P = prod over rays (decreasing slope) of exp(sum om[a] x^a/(y-1/y)); return all om[a] *)
factorAll[P0_Association, rays_List, gam_, Mat_] := Module[{P = P0, R, res = <||>},
  Do[
   R = rayLog[KeySelect[P, MemberQ[ray, #] || # == 0 gam &], gam];
   KeyValueMap[(res[#1] = simp[#2 (y - 1/y)]) &, R];
   If[Length[R] > 0, P = DeleteCases[Map[simp, qtMul[qtExp[-R, Mat, gam], P, Mat, gam]], 0]],
   {ray, rays}];
  res];

checkRays[rays_, c_] := Scan[If[MatrixRank[#] > 1, Message[KSWallCrossingRat::ray, #, c]] &, rays];

KSWallCrossingRat[Mat_, Omb1_, c1_, c2_, Nvec_, OptionsPattern[]] := Block[{$ksPattern = OptionValue["CollectPattern"]},
  Module[{charges, om1, r1, r2, P, res},
   charges = Append[subVecs[Nvec], Nvec];
   om1 = Association[Map[# -> If[AssociationQ[Omb1], Lookup[Omb1, Key[#], 0], Omb1[#]] &, charges]];
   om1 = Select[om1, # =!= 0 &];
   r1 = raysByDecreasingSlope[charges, toLex[c1]]; checkRays[r1, c1];
   r2 = raysByDecreasingSlope[charges, toLex[c2]]; checkRays[r2, c2];
   P = qtProduct[Map[Select[#, KeyExistsQ[om1, #] &] &, r1], om1, Mat, Nvec];
   res = factorAll[P, r2, Nvec, Mat];
   Association[Map[# -> Lookup[res, Key[#], 0] &, SortBy[charges, {Total, Identity}]]]]];

KSWallCrossing[Mat_, Om1_, c1_, c2_, Nvec_, opts : OptionsPattern[]] := Module[{om, omb1, omb2},
  om[a_, yy_] := If[AssociationQ[Om1], Lookup[Om1, Key[a], 0] /. y -> yy, Om1[a, yy]];
  omb1[a_] := DivisorSum[GCD @@ a, (y - 1/y)/(# (y^# - y^(-#))) om[a/#, y^#] &];
  omb2 = KSWallCrossingRat[Mat, omb1, c1, c2, Nvec, opts];
  Association[KeyValueMap[Function[{a, v}, a -> Block[{$ksPattern = OptionValue[KSWallCrossing, {opts}, "CollectPattern"]},
       simp[DivisorSum[GCD @@ a, MoebiusMu[#]/# (y - 1/y)/(y^# - y^(-#)) (omb2[a/#] /. y -> y^#) &]]]], omb2]]];

(* ---------- the recursion ---------- *)
memo = <||>; nWalls = 0;
FastFlowTreeClear[] := (memo = <||>; nWalls = 0;);

omBar[Mat_, OmS_, gam_List, c0_List] := Module[{c = normalizeC[c0, gam], key, val},
  key = {Mat, OmS, gam, c};
  val = Lookup[memo, Key[key], Missing[]];
  If[MissingQ[val], val = omBarCompute[Mat, OmS, gam, c]; memo[key] = val];
  val];

omBarCompute[Mat_, OmS_, gam_, c_] := Module[
  {subs, walls, cur, cstar, lam, pairing, wl, grp, Lam, S, cw, cminus, cplus, om, raysM, P},
  cstar = gam . Mat;            (* cstar . a = <gam, a> *)
  subs = subVecs[gam];
  (* walls: d with <d,gam> > 0 and lambda = (c.d)/<d,gam> > 0 *)
  walls = {};
  Do[pairing = d . Mat . gam;
   If[pairing > 0,
    lam = Map[# . d &, c]/pairing;
    If[lexSign[lam] > 0, AppendTo[walls, {lam, d}]]],
   {d, subs}];
  cur = If[OmS === Automatic, OmAttb[gam, y], omStarBar[OmS, gam, y]];
  If[Length[walls] == 0, Return[cur]];
  (* group by wall position, decreasing lambda (we go from the attractor point back to c) *)
  walls = GatherBy[walls, First];
  walls = Sort[walls, lexLess[#2[[1, 1]], #1[[1, 1]]] &];
  Do[
   nWalls++;
   wl = grp[[1, 1]];
   Lam = Append[grp[[All, 2]], gam];
   If[MatrixRank[Lam] != 2,
    Message[FastFlowTreeFormula::rank, gam, c, grp[[All, 2]]]];
   (* all charges of the rank-2 sublattice which are <= gam *)
   S = Select[subs, MatrixRank[{gam, grp[[1, 2]], #}] == 2 &];
   cw = MapThread[#1 + #2 cstar &, {c, wl}];       (* point on the wall *)
   cminus = Append[cw, cstar];                    (* just after the wall, towards attractor *)
   cplus = Append[cw, -cstar];                    (* just before the wall *)
   om = Association[Map[# -> omBar[Mat, OmS, #, cminus] &, S]];
   om[gam] = cur;
   S = Append[S, gam];
   raysM = raysByDecreasingSlope[S, cminus];
   P = qtProduct[raysM, om, Mat, gam];
   cur = peel[P, raysByDecreasingSlope[S, cplus], gam, Mat],
   {grp, walls}];
  cur];

FastFlowTreeFormula::rank = "Accidental wall: charges `3` of `1` at `2` do not span a rank 2 lattice; results may be wrong. Perturb the FI parameters.";

FastFlowTreeFormulaRat[Mat_, Cvec_, Nvec_, OmS_: Automatic] := Module[{c},
  If[Total[Nvec] == 0, Return[0]];
  c = {Cvec - (Nvec . Cvec)/Total[Nvec]};
  nWalls = 0;
  collectOm[omBar[Mat, OmS, Nvec, c]]];

(* simplify coefficient of each monomial in the attractor indices separately (much cheaper than Factor) *)
collectOm[e_] := Collect[Expand[e], {_OmAttb, _OmAtt}, Factor];

FastFlowTreeFormula[Mat_, Cvec_, Nvec_, OmS_: Automatic] := Module[{res},
  If[Total[Nvec] == 0, Return[0]];
  res = DivisorSum[GCD @@ Nvec,
    MoebiusMu[#]/# (y - 1/y)/(y^# - y^(-#)) (FastFlowTreeFormulaRat[Mat, Cvec, Nvec/#, OmS] /. y -> y^#) &];
  If[OmS === Automatic, collectOm[OmAttbToOmAtt[res]], collectOm[res]]];

FastFlowTreeStats[] := {Length[memo], nWalls};

End[];
EndPackage[];


(* ===================== Coulomb index with memoization ===================== *)
(* Same algorithm as CoulombIndexOpt (sum over permutations of the recursion for F and G),
   but F and G are memoized on their exact (perturbed) arguments within one evaluation:
   sub-calls depend only on prefixes / contiguous blocks of the permutation and are shared
   among many permutations. *)
Begin["CoulombHiggs`Private`"];
defineMemoFG[]:=(
memoF[Mat_,Cvec_]:=memoF[Mat,Cvec]=
        Module[{m=Length[Mat]},
  If[m>1,
    If[Mat[[m-1,m]] Cvec[[m]]<0,  If[Mat[[m-1,m]]>0,1,-1]
    memoF[Take[Mat, {1, m-1}, {1, m-1}], Flatten[{Take[Cvec, {1,m-2}],
            Cvec[[m-1]]+ Cvec[[m]]}]],0]
        +If[$QuiverNoLoop,0,
        Sum[
        If[-Sum[Sum[Mat[[i,j]],{j, i+1,m}], {i,k+1,m-1}] 
            Sum[Sum[Mat[[i,j]],{j, i+1,m-1}], {i,k+1,m-2}] >0,
          If[Sum[Mat[[i,m]], {i,k+1,m-1}]>0,
          memoF[MNewFOpt[Mat,k], CNewF[Cvec,k]] memoG[MNewGOpt[Mat,k]],
          -memoF[MNewFOpt[Mat,k], CNewF[Cvec,k]] memoG[MNewGOpt[Mat,k]]
          ],
        If[-Sum[Sum[Mat[[i,j]],{j, i+1,m}], {i,k+1,m-1}] 
            Sum[Sum[Mat[[i,j]],{j, i+1,m-1}], {i,k+1,m-2}]==0,
          If[$QuiverVerbose, Message[UnitStepWarn::zero]]
          If[Sum[Mat[[i,m]], {i,k+1,m-1}]>0,
          1/2 memoF[MNewFOpt[Mat,k], CNewF[Cvec,k]] memoG[MNewGOpt[Mat,k]],
          -1/2 memoF[MNewFOpt[Mat,k], CNewF[Cvec,k]] memoG[MNewGOpt[Mat,k]]
          ]
        ,0]], 
        {k, 0, m-3}]],
 If[m==1,1,0]
]];

(* induction rule for G *)
memoG[Mat_]:=memoG[Mat]=Module[{m=Length[Mat],g=0.,mu1,mu2,i=1,j=1,k=1},
If[m==3,If[Mat[[1,2]]Mat[[2,3]]>0,If[Mat[[1,2]]>0,g=1,g=-1],g=0],If[m==2,g=1,
If[m==1, g=1,
If[ m>3,
mu1=-Mat[[m-2,m-1]]/(Mat[[m-2,m]]+Mat[[m-1,m]]);
mu2=(Sum[Mat[[i,j]],{i,2,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Mat[[1,m]];
g=(* value at mu=0 *)Plus@@{
   If[Mat[[m-1,m]]Sum[Mat[[i,m]],{i,m-1}]<0,
     If[Mat[[m-1,m]]>0,
       memoG[Take[MatmuOpt[Mat,0],{1,m-1},{1,m-1}]],
      -memoG[Take[MatmuOpt[Mat,0],{1,m-1},{1,m-1}]]],   
   If[Mat[[m-1,m]]Sum[Mat[[i,m]],{i,m-1}]<0,
     If[$QuiverVerbose, Message[UnitStepWarn::zero]]
     If[Mat[[m-1,m]]==0,
       1/2 memoG[Take[MatmuOpt[Mat,0],{1,m-1},{1,m-1}]],
      -1/2 memoG[Take[MatmuOpt[Mat,0],{1,m-1},{1,m-1}]]],
   0]]
,(* type 1 contribution: (m-2,m-1,m) form scaling subset *)
 If[(Mat[[m-2,m-1]]+Mat[[m-1,m]]+Mat[[m-2,m]])Mat[[m-2,m-1]]<0,
   If[Mat[[m-2,m]]+Mat[[m-1,m]]>0,
    memoG[MatRedOpt[MatmuOpt[Mat,mu1],m-2]] memoG[Take[MatmuOpt[Mat,mu1],{m-2,m},{m-2,m}]],
   -memoG[MatRedOpt[MatmuOpt[Mat,mu1],m-2]] memoG[Take[MatmuOpt[Mat,mu1],{m-2,m},{m-2,m}]]]
   ,
  If[(Mat[[m-2,m-1]]+Mat[[m-1,m]]+Mat[[m-2,m]])Mat[[m-2,m-1]]==0,
   If[$QuiverVerbose, Message[UnitStepWarn::zero]]
   If[Mat[[m-2,m]]+Mat[[m-1,m]]>0,
    1/2 memoG[MatRedOpt[MatmuOpt[Mat,mu1],m-2]] memoG[Take[MatmuOpt[Mat,mu1],{m-2,m},{m-2,m}]],
   -1/2 memoG[MatRedOpt[MatmuOpt[Mat,mu1],m-2]] memoG[Take[MatmuOpt[Mat,mu1],{m-2,m},{m-2,m}]]]
   ,
  0]],
(* type 2 contribution, k=2: (2,...m-3) form scaling subset *)
If[m>4, 
     If[Sum[Mat[[i,j]],{i,2,m-1},{j,i+1,m}]
        (Sum[Mat[[i,j]],{i,2,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])<0,If[Mat[[1,m]]>0,-memoG[Take[MatmuOpt[Mat,mu2],{2,m},{2,m}]],memoG[Take[MatmuOpt[Mat,mu2],{2,m},{2,m}]]],0] 
    ,0],(* type 2 contributions, k>2 *)	Sum[Module[{mu3=(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Sum[Mat[[i,m]],{i,k-1}]},
	If[(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m}])
		(Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])<0,
     If[Sum[Mat[[i,m]],{i,k-1}]>0,
      -memoG[MatRedOpt[MatmuOpt[Mat,mu3],k]] memoG[Take[MatmuOpt[Mat,mu3],{k,m},{k,m}]] , 
      memoG[MatRedOpt[MatmuOpt[Mat,mu3],k]] memoG[Take[MatmuOpt[Mat,mu3],{k,m},{k,m}]] ]
    ,
	If[(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m}])
		(Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])==0,
     If[$QuiverVerbose, Message[UnitStepWarn::zero]]
     If[Sum[Mat[[i,m]],{i,k-1}]>0,
      -1/2 memoG[MatRedOpt[MatmuOpt[Mat,mu3],k]] memoG[Take[MatmuOpt[Mat,mu3],{k,m},{k,m}]] , 
      1/2 memoG[MatRedOpt[MatmuOpt[Mat,mu3],k]] memoG[Take[MatmuOpt[Mat,mu3],{k,m},{k,m}]] ]
    ,0]]],{k,3,m-3}],
(* type 3 contributions *)	
 Sum[Module[{mu4=(Sum[Mat[[i,j]],{i,k,m-1},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])/Sum[Mat[[i,m]],{i,m-1}]},
    If[(Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}])
     (Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])<0,
    If[Sum[Mat[[i,m]],{i,m-1}]>0,
      -memoG[MatRedOpt2[MatmuOpt[Mat,mu4],k]]memoG[Take[MatmuOpt[Mat,mu4],{k,m-1},{k,m-1}]], 
      memoG[MatRedOpt2[MatmuOpt[Mat,mu4],k]] memoG[Take[MatmuOpt[Mat,mu4],{k,m-1},{k,m-1}]]]
    ,
    If[(Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}])
     (Sum[Mat[[i,j]],{i,k,m-2},{j,i+1,m-1}]+Sum[Mat[[i,m]],{i,m-1}])==0,
     If[$QuiverVerbose, Message[UnitStepWarn::zero]]
    If[Sum[Mat[[i,m]],{i,m-1}]>0,
      -1/2 memoG[MatRedOpt2[MatmuOpt[Mat,mu4],k]]memoG[Take[MatmuOpt[Mat,mu4],{k,m-1},{k,m-1}]], 
      1/2 memoG[MatRedOpt2[MatmuOpt[Mat,mu4],k]] memoG[Take[MatmuOpt[Mat,mu4],{k,m-1},{k,m-1}]]]
    ,0]]],{k,2,m-3}]},g=0;]]];g]]
);
defineMemoFG[];

FastCoulombIndex[Mat_,PMat_,Cvec_,y_]:=Module[{m,ListPerm,RMat,RCvec,res},
	m=Length[Cvec];
	ListPerm=Permutations[Range[m]];
	RMat=Table[Random[Integer,{1,100000}],{i,m},{j,m}];
	RMat=1/100000/$QuiverPerturb2 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,m},{j,m}];
	RCvec=1/1000/$QuiverPerturb2 Table[Random[Integer,{1,1000}],{i,m}];
	RCvec[[m]]=-Sum[RCvec[[i]],{i,m-1}];
    Clear[memoF,memoG]; defineMemoFG[];
	res=(y-1/y)^(1-m) (-1)^(Sum[QuiverMultiplierMat[i,j] Mat[[i,j]],{i,m},{j,i+1,m}]+m-1)
	Sum[With[{p=ListPerm[[k]]},y^(Sum[QuiverMultiplierMat[p[[i]],p[[j]]] Mat[[p[[i]],p[[j]]]],{i,m},{j,i+1,m}])
		memoF[(PMat+RMat)[[p,p]], (Cvec+RCvec)[[p]]]], {k,Length[ListPerm]}];
    Clear[memoF,memoG]; defineMemoFG[];
    res];
End[];

(* ===================== compiled Coulomb index ===================== *)
Begin["CoulombHiggs`Private`"];
(* default: closed Poincare-Hopf formula (c/coulombph); c/coulombidx (translation of the recursion) is used
   when $QuiverNoLoop is set, which the closed formula does not implement *)
If[!ValueQ[$CoulombIdxExe], $CoulombIdxExe = FileNameJoin[{DirectoryName[$InputFileName], "c", "coulombph"}]];
If[!ValueQ[$CoulombIdxRecExe], $CoulombIdxRecExe = FileNameJoin[{DirectoryName[$InputFileName], "c", "coulombidx"}]];
If[!ValueQ[$CoulombIdxThreads], $CoulombIdxThreads = 8];
$CoulombIdxFallbacks = 0;
$CoulombIdxDoubleDouble = 0;
If[!ValueQ[$FastPerturbRange], $FastPerturbRange = 10^5];
$CoulombIdxLastFailure = None;

(* exact rationals p/q when numerator and denominator fit in 63 bits, decimals otherwise *)
numStr[x_] := If[(IntegerQ[x] || Head[x] === Rational) && Max[Abs[Numerator[x]], Denominator[x]] < 2^62,
   ToString[Numerator[x]] <> "/" <> ToString[Denominator[x]], ToString[CForm[N[x, 20]]]];

(* batch evaluation: probs = list of {Mat, perturbed PMat, perturbed Cvec}; returns the list of
   Coulomb indices (in the variable yy), or $Failed for those flagged AMBIGUOUS *)
cBatch[probs_List, yy_] := Module[{ins, out, blocks, E, m},
  If[Length[probs] == 0, Return[{}]];
  ins = Map[Function[pr, m = Length[pr[[1]]];
      E = Table[QuiverMultiplierMat[i, j] pr[[1, i, j]], {i, m}, {j, m}];
      If[! MatrixQ[E, IntegerQ], Return[$Failed, Module]];
      StringRiffle[Join[{m, $CoulombIdxThreads, If[TrueQ[$QuiverNoLoop], 1, 0]}, Flatten[E],
         Map[numStr, Flatten[pr[[2]]]], Map[numStr, pr[[3]]]], " "]], probs];
  out = RunProcess[{If[TrueQ[$QuiverNoLoop], $CoulombIdxRecExe, $CoulombIdxExe]}, "StandardOutput", StringRiffle[ins, "\n"] <> "\n"];
  If[! StringQ[out], $CoulombIdxLastFailure = {ins, out}; $CoulombIdxFallbacks += Length[probs]; Return[ConstantArray[$Failed, Length[probs]]]];
  (* an index may vanish (no line before END): keep empty blocks *)
  blocks = Map[StringSplit[StringTrim[#], "\n"] &, Most[StringSplit[out, "END\n", All]]];
  If[Length[blocks] != Length[probs], $CoulombIdxLastFailure = {ins, out}; $CoulombIdxFallbacks += Length[probs]; Return[ConstantArray[$Failed, Length[probs]]]];
  MapThread[Function[{pr, bl}, Module[{lines, mm = Length[pr[[1]]], EE},
      lines = Map[StringSplit, Select[bl, StringLength[StringTrim[#]] > 0 &]];
      If[MemberQ[lines[[All, 1]], "DOUBLEDOUBLE"], $CoulombIdxDoubleDouble++; lines = DeleteCases[lines, {"DOUBLEDOUBLE"} | {"DDZEROS", _}]];
      If[MemberQ[lines[[All, 1]], "AMBIGUOUS"], $CoulombIdxFallbacks++; $Failed,
       EE = Table[QuiverMultiplierMat[i, j] pr[[1, i, j]], {i, mm}, {j, mm}];
       (yy - 1/yy)^(1 - mm) (-1)^(Sum[EE[[i, j]], {i, mm}, {j, i + 1, mm}] + mm - 1)
        Total[Map[yy^ToExpression[#[[1]]] (Round[2^30 Internal`StringToMReal[#[[2]]]]/2^30) &, lines]]]]],
   {probs, blocks}]];

(* same magnitudes as CoulombIndexOpt, but the per-centre FI shift is drawn from $FastPerturbRange
   values instead of 1000 (coincidences between subset sums of the shifts leave walls unresolved) *)
perturbCI[Mat_, PMat_, Cvec_] := Module[{m = Length[Cvec], RMat, RCvec, K = $FastPerturbRange},
	RMat=Table[Random[Integer,{1,100000}],{i,m},{j,m}];
	RMat=1/100000/$QuiverPerturb2 Table[Which[i<j,RMat[[i,j]],i>j,-RMat[[j,i]],i==j,0],{i,m},{j,m}];
	RCvec=1/K/$QuiverPerturb2 Table[Random[Integer,{1,K}],{i,m}];
	RCvec[[m]]=-Sum[RCvec[[i]],{i,m-1}];
    {Mat, PMat + RMat, Cvec + RCvec}];

CCoulombIndexPerturbed[Mat_, PP_, CC_, y_] := First[cBatch[{{Mat, PP, CC}}, y]];

CCoulombIndex[Mat_, PMat_, Cvec_, y_] := Module[{r},
    r = First[cBatch[{perturbCI[Mat, PMat, Cvec]}, y]];
    If[r === $Failed, CoulombIndexOpt[Mat, PMat, Cvec, y], r]];

(* evaluate all Coulombg[Li,y] factors in f, the large ones in a single call of the program *)
evalCoulombgBatch[f_, data_] := Module[{gs, big, small, probs, vals, rules},
  gs = DeleteDuplicates[Cases[f, Coulombg[_, _], {0, Infinity}]];
  big = If[$QuiverCoulombOpt == 2 && FileExistsQ[$CoulombIdxExe], Select[gs, Length[#[[1]]] >= 5 &], {}];
  small = Complement[gs, big];
  probs = Map[perturbCI @@ data[#[[1]]] &, big];
  vals = cBatch[probs, \[FormalY]];
  rules = Join[
    MapThread[Function[{g, v}, g -> If[v === $Failed, CoulombIndexOpt @@ Append[data[g[[1]]], g[[2]]], v /. \[FormalY] -> g[[2]]]], {big, vals}],
    Map[# -> coulombDispatch @@ Append[data[#[[1]]], #[[2]]] &, small]];
  f /. Dispatch[rules]];
End[];

(* ===================== overrides of CoulombHiggs internals ===================== *)
(* Loaded only when this file is loaded; set $QuiverCoulombOpt = 1 to recover the original
   Mathematica evaluation of the Coulomb indices. *)
Begin["CoulombHiggs`Private`"];

(* TestNoLoop: the original enumerates all m! orderings; here an equivalent acyclicity test
   (an ordering with MatProd[[s_i,s_j]]>=0 for all i<j exists iff the digraph u->v for
   MatProd[[u,v]]>0 has no oriented cycle). *)
acyclicQ[A_] := Module[{m = Length[A], indeg, queue, seen = 0, u},
  indeg = Table[Count[A[[All, v]], _?Positive], {v, m}];
  queue = Flatten[Position[indeg, 0]];
  While[Length[queue] > 0,
   u = First[queue]; queue = Rest[queue]; seen++;
   Do[If[A[[u, v]] > 0, indeg[[v]]--; If[indeg[[v]] == 0, AppendTo[queue, v]]], {v, m}]];
  seen == m];

TestNoLoop[Mat_,Li_]:=Module[{m,MatProd},
	m=Length[Li];
    Which[
	  $QuiverOmSbasis==0,False,
      m==1,False,
      m==2,True,
      $QuiverNoLoop,True,
      !$QuiverTestLoop,False,
      $QuiverTestLoop,
	    MatProd=Li . Mat . Transpose[Li];
	    acyclicQ[MatProd]
	]
];

(* memoized partitions *)

(* Coulomb indices: $QuiverCoulombOpt==2 (default here) uses the compiled program for >= 5 centers *)
coulombDispatch[M_, PM_, C_, y_] := Which[
   $QuiverCoulombOpt == 1 || $QuiverCoulombOpt == 2, CoulombIndexOpt[M, PM, C, y],
   True, CoulombIndex[M, PM, C, y]];

EvalCoulombIndex[Mat_,PMat_,Cvec_,f_]:=evalCoulombgBatch[f,
  Function[Li, {Li . Mat . Transpose[Li], Li . PMat . Transpose[Li], Li . Cvec}]];

EvalCoulombIndexAtt[Mat_,PMat_,f_]:=evalCoulombgBatch[f,
  Function[Li, {Li . Mat . Transpose[Li], Li . PMat . Transpose[Li], -Total[Li . PMat . Transpose[Li], {2}]}]];



$QuiverCoulombOpt = 2;
End[];

(* ===================== Coulomb branch formula with sparse polynomials ===================== *)
(* Same algorithm, perturbations, zero rules, H-factor determination and minimal modification as
   CoulombBranchFormula, but intermediate results are kept as sparse polynomials
   <| sorted list of factors -> coefficient (rational function of y) |>, with factors
   {1, alpha, k} = OmS[alpha, y^k] and {2, charges, mults, k} = CoulombH[charges, mults, y^k].
   Vanishing factors are dropped before multiplying, partitions with vanishing Coulomb index are
   skipped, and only sub-dimension vectors carrying undetermined H-factors are treated. *)
Begin["CoulombHiggs`Private`"];

symFactor[pa_] := 1/Times @@ (Factorial /@ Tally[pa][[All, 2]]);
diagLi[b_] := Select[Table[If[j == i, b[[j]], 0], {j, Length[b]}, {i, Length[b]}], # != 0 b &];
omSZero[Mat_, b_] := TestNoLoop[Mat, diagLi[b]] ||
   (Total[b] > 1 && Union[b] == {0, Total[b]} && $QuiverOmSbasis =!= 0);

SetAttributes[pAddTo, HoldFirst];
pAddTo[acc_, p_, c_] := KeyValueMap[(acc[#1] = Lookup[acc, Key[#1], 0] + c #2) &, p];
pMul[p_, q_] := Module[{r = <||>, k},
  KeyValueMap[Function[{k1, c1}, KeyValueMap[Function[{k2, c2},
       k = Sort[Join[k1, k2]]; r[k] = Lookup[r, Key[k], 0] + c1 c2], q]], p]; r];

(* OmT[b, y^k] after OmTToOmS and the zero rules *)
omTPoly[Mat_, PMat_, b_, k_] := Module[{res = <||>, L},
  If[TestNoLoop[PMat, diagLi[b]], Return[res]];
  If[! omSZero[Mat, b], res[{{1, b, k}}] = 1];
  Do[If[Length[L] > 2 && ! TestNoLoop[PMat, L[[All, 1]]] && NoneTrue[L, omSZero[Mat, #[[1]]] &],
     res[Sort[Prepend[Map[{1, #[[1]], k #[[2]]} &, L], {2, L[[All, 1]], L[[All, 2]], k}]]] = 1],
   {L, ListAllPartitionsMult[b]}];
  res];

(* Poincare polynomial (with OmS, CoulombH factors) of N at FI Cvec, as sparse polynomial *)
qpPoly[Mat_, PMat_, Cvec_, N_] := Module[{tomT = <||>, tomTR = <||>, omT, omTR, parts, gs, vals, gval = <||>,
   acc = <||>, big, small, term, f, P, d, prods = {}},
  omT[b_, k_] := If[KeyExistsQ[tomT, {b, k}], tomT[{b, k}], tomT[{b, k}] = omTPoly[Mat, PMat, b, k]];
  omTR[a_, dd_] := If[KeyExistsQ[tomTR, {a, dd}], tomTR[{a, dd}], tomTR[{a, dd}] = Module[{r = <||>},
      Do[pAddTo[r, omT[a/e, dd e], (y^dd - y^-dd)/(e (y^(dd e) - y^(-dd e)))], {e, Divisors[GCD @@ a]}];
      DeleteCases[Map[Together, r], 0]]];
  parts = Flatten[Map[Function[dd, Map[{dd, #} &, ListAllPartitions[N/dd]]], Divisors[GCD @@ N]], 1];
  (* drop partitions with a vanishing OmT factor before computing any Coulomb index *)
  parts = Select[parts, Function[pd, AllTrue[pd[[2]], Length[omTR[#, pd[[1]]]] > 0 &]]];
  gs = DeleteDuplicates[parts[[All, 2]]];
  big = If[$QuiverCoulombOpt == 2 && FileExistsQ[$CoulombIdxExe], Select[gs, Length[#] >= 5 &], {}];
  small = Complement[gs, big];
  vals = cBatch[Map[perturbCI[# . Mat . Transpose[#], # . PMat . Transpose[#], # . Cvec] &, big], y];
  MapThread[(gval[#1] = If[#2 === $Failed, CoulombIndexOpt[#1 . Mat . Transpose[#1], #1 . PMat . Transpose[#1], #1 . Cvec, y], #2]) &, {big, vals}];
  If[$QuiverVerbose, Print["qpPoly ", N, ": ", Length[parts], " partitions, ", Length[big], " large indices, fallbacks so far ", $CoulombIdxFallbacks]];
  Scan[(gval[#] = If[Length[#] == 1, 1, CoulombIndexOpt[# . Mat . Transpose[#], # . PMat . Transpose[#], # . Cvec, y]]) &, small];
  If[$QuiverVerbose, Print["qpPoly ", N, ": small indices done"]];
  Do[
   {d, P} = pd;
   f = Together[gval[P] /. y -> y^d];
   If[f =!= 0,
    term = <|{} -> MoebiusMu[d]/d (y - 1/y)/(y^d - y^-d) symFactor[P] f|>;
    Do[term = pMul[term, omTR[a, d]], {a, P}];
    pAddTo[acc, term, 1]],
   {pd, parts}];
  If[$QuiverVerbose, Print["qpPoly ", N, ": ", Length[acc], " monomials"]];
  DeleteCases[Map[Together, acc], 0]];

(* value of a sparse-polynomial key with known H values substituted; unknown H returned as symbol *)
hSubst[key_, hv_] := Times @@ Map[If[#[[1]] == 1, OmSf[#[[2]], #[[3]]],
      With[{v = Lookup[hv, Key[{#[[2]], #[[3]]}], Missing[]]},
       If[MissingQ[v], Hsym[#[[2]], #[[3]], #[[4]]], v /. y -> y^#[[4]]]]] &, key];

(* solve for the H factors of dimension vector N from its sparse Poincare polynomial *)
solveH[Mat_, PMat_, N_, qp_, hv_] := Module[{Ls, sol = <||>, coef, mono, eqs, unk, so},
  Ls = Select[ListAllPartitionsMult[N], Length[#] > 2 && ! TestNoLoop[PMat, #[[All, 1]]] &&
      NoneTrue[#, omSZero[Mat, #[[1]]] &] &];
  If[Length[Ls] == 0, Return[sol]];
  eqs = {}; unk = {};
  Do[mono = Sort[Map[{1, #[[1]], #[[2]]} &, L]];
   coef = Total[KeyValueMap[If[Select[#1, First[#] == 1 &] == mono, #2 (hSubst[Select[#1, First[#] == 2 &], hv]), 0] &, qp]];
   If[! FreeQ[coef, Hsym[L[[All, 1]], L[[All, 2]], 1]],
    AppendTo[eqs, coef == 0]; AppendTo[unk, Hsym[L[[All, 1]], L[[All, 2]], 1]]],
   {L, Ls}];
  If[Length[unk] == 0, Return[sol]];
  If[$QuiverVerbose, Print["solveH ", N, ": ", Length[unk], " H-factors"]];
  so = Simplify[Solve[eqs, unk][[1]]];
  Do[With[{h = u /. so}, sol[{u[[1]], u[[2]]}] =
      Simplify[Simplify[-MinimalModif[h] + h], $QuiverMultiplierAssumption \[Element] Integers]], {u, unk}];
  sol];

(* as RandomFI, with $FastPerturbRange values instead of 2001 *)
fineRandomFI[gam_] := Module[{m = Length[gam], nz, k, Cvec, K = $FastPerturbRange},
  nz = Select[Range[m], gam[[#]] > 0 &];
  If[Length[nz] == 0, Return[0 gam]];
  k = Last[nz]; Cvec = RandomInteger[{-K, K}, m]/(K/1000);
  Cvec[[k]] = -Sum[If[i == k, 0, gam[[i]] Cvec[[i]]], {i, m}]/gam[[k]];
  Cvec/$QuiverPerturb1];

needsH[Mat_, PMat_, N_] := AnyTrue[ListAllPartitionsMult[N], Length[#] > 2 && ! TestNoLoop[PMat, #[[All, 1]]] &&
     NoneTrue[#, omSZero[Mat, #[[1]]] &] &];

FastCoulombBranchFormula[Mat_, Cvec_, Nvec_] := Module[{RMat, PMat, Cvec0, hv = <||>, subs, qp, res, hrules},
  If[Plus @@ Nvec == 0, Return[0]];
  If[Plus @@ Nvec == 1, Return[1]];
  Cvec0 = Cvec - (Plus @@ (Nvec Cvec))/(Plus @@ Nvec);
  RMat = Table[Random[Integer, {1, $FastPerturbRange}], {i, Length[Mat]}, {j, Length[Mat]}];
  RMat = 1/$FastPerturbRange/$QuiverPerturb1 Table[Which[i < j, RMat[[i, j]], i > j, -RMat[[j, i]], i == j, 0], {i, Length[Mat]}, {j, Length[Mat]}];
  PMat = Mat + RMat;
  If[! TrueQ[$QuiverNoLoop],
   (* H factors of sub-dimension vectors, at their attractor point, by increasing total dimension *)
   subs = SortBy[Select[ListSubQuivers[Nvec], 3 <= Total[#] <= Total[Nvec] - 1 &], Total];
   Do[If[needsH[Mat, PMat, a],
     qp = qpPoly[Mat, PMat, AttractorFI[Mat, a] + fineRandomFI[a]/$QuiverPerturb1, a];
     hv = Join[hv, solveH[Mat, PMat, a, qp, hv]]], {a, subs}]];
  qp = qpPoly[Mat, PMat, Cvec0, Nvec];
  If[! TrueQ[$QuiverNoLoop] && needsH[Mat, PMat, Nvec], hv = Join[hv, solveH[Mat, PMat, Nvec, qp, hv]]];
  res = Total[KeyValueMap[#2 hSubst[#1, hv] &, qp]] /. Hsym[__] -> 0 /. OmSf[a_, k_] :> OmS[a, y^k];
  res = SwapFugacity[SimplifyOmSbasis[res]];
  If[$QuiverDisplayCoulombH,
   hrules = KeyValueMap[CoulombH[#1[[1]], #1[[2]], y] -> #2 &, hv]; {res, hrules}, res]];

CoulombBranchFormula[Mat_, Cvec_, Nvec_] /; ($QuiverCoulombOpt == 2 && ! TrueQ[$inFastCB]) :=
  Block[{$inFastCB = True}, FastCoulombBranchFormula[Mat, Cvec, Nvec]];
DownValues[CoulombBranchFormula] = RotateRight[DownValues[CoulombBranchFormula]];
End[];
