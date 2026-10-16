(**********************************************************************)
(* Lambda algebra definitions                                         *)

modp[x_] := PolynomialMod[x,2]

DigitString[n_Integer] := n /; n<10

DigitString[n_Integer] :=
 Module[{d,e},
  d = IntegerDigits[n];
  e = Drop[d,1];
  SequenceForm[d[[1]],UnderBar[SequenceForm @@ e]]
 ]

Format[lambda[i__]] :=
 Subscript[\[Lambda],SequenceForm @@ (DigitString /@ {i})]

Format[lambda[]] = Subscript[\[Lambda],"\[EmptySet]"]

Format[ulambda[n_,i__]] :=
 Subsuperscript[
  \[Lambda],
  SequenceForm @@ (DigitString /@ {i}),
  SequenceForm["(",n,")"]
 ]

Format[ulambda[n_]] :=
 Subsuperscript[\[Lambda],"\[EmptySet]",SequenceForm["(",n,")"]]

Bidegree[lambda[i___]] := 
 {Length[{i}],Plus @@ ({i} + 1)}

Bidegree[ulambda[n_,i___]] := 
 {Length[{i}],Plus @@ ({i} + 1)}

Bidegree[x_Plus] :=
 Module[{l},
  l = Bidegree /@ (List @@ x);
  If[Equal @@ l,First[l],Inhomogeneous]
 ]

Tridegree[ulambda[n_,i___]] := 
 {n,Length[{i}],Plus @@ ({i} + 1)}

Tridegree[x_Plus] :=
 Module[{l},
  l = Tridegree /@ (List @@ x);
  If[Equal @@ l,First[l],Inhomogeneous]
 ]

AdamsFiltration[0] = Infinity
AdamsFiltration[lambda[i___]]     := Length[{i}]
AdamsFiltration[ulambda[n_,i___]] := Length[{i}]
AdamsFiltration[x_Plus] :=
 Min @@ (AdamsFiltration /@ (List @@ x))
AdamsFiltration[a_] := 
 AdamsFiltration[LambdaRepresentative[a]]
 
Stem[lambda[i___]] := Plus[i]

Stem[ulambda[n_,i___]] := Plus[i]

Stem[x_Plus] :=
 Module[{l},
  l = Stem /@ (List @@ x);
  If[Equal @@ l,First[l],Inhomogeneous]
 ]

SourceSphere[ulambda[n_,i___]] := Plus[n,i]
TargetSphere[ulambda[n_,i___]] := n

o[x_Plus,y_lambda]      :=
 PolynomialMod[o[#,y] & /@ x,2]
o[n_?EvenQ x_,y_lambda] := 0
o[n_?OddQ x_,y_lambda]  := o[x,y]
lambda /: n_?EvenQ x_lambda := 0
lambda /: n_?OddQ x_lambda  := x

o[x_Plus,y_ulambda]      :=
 PolynomialMod[o[#,y] & /@ x,2]
o[n_?EvenQ x_,y_ulambda] := 0
o[n_?OddQ x_,y_ulambda]  := o[x,y]
ulambda /: n_?EvenQ x_ulambda := 0
ulambda /: n_?OddQ x_ulambda  := x

o[lambda[i___],lambda[j___]] := lambdared[i,j]
o[ulambda[n_,i___],lambda[j___]] :=
 (lambdared[i,j] /. lambda[k___] :> ulambda[n,k])
o[ulambda[n_,i___],ulambda[m_,j___]] :=
 (lambdared[i,j] /. lambda[k___] :> ulambda[n,k]) /; Plus[n,i] === m

Sigma[lambda[i___]]     := lambda[i]
Sigma[ulambda[n_,i___]] := ulambda[n+1,i]

Hopf[ulambda[n_]] := 0
Hopf[ulambda[n_,i__]] :=
 lambdared[i] /. 
  (lambda[p_,q___] :> If[p == n-1,ulambda[2n-1,q],0])

WhiteheadP[ulambda[m_?OddQ,i___]] :=
 del[o[lambda[(m-1)/2],lambda[i]]] /. lambda[j___] :> ulambda[(m-1)/2,j]

bc[n_,m_] := (bc[n,m] = Mod[Binomial[n,m],2])

admissibleQ[i___] := And @@ (Not /@ Negative /@ (2{Infinity,i}-{i,0}))

lambdared[k___] := 
 (lambdared[k] =
  Module[{lk,t,left,right,i,j,n},
   If[admissibleQ[k],
     lambda[k],
     lk = {k};
     t=1;
     While[lk[[t+1]] <= 2 lk[[t]], t++];
     left  = lambda @@ lk[[Range[t-1]]];
     right = lambdared @@ lk[[Range[t+2,Length[lk]]]];
     i = lk[[t]];
     n = lk[[t+1]] - 2i - 1;
     PolynomialMod[
      Sum[ bc[n-1-j,j] o[left,lambdared[i+n-j,2i+1+j],right],
           {j,0,Floor[(n-1)/2]}],
      2
     ]
   ]
  ])

dlambda[n_] :=
 (dlambda[n] =
   PolynomialMod[
    Expand[Sum[bc[n-j,j] lambdared[n-j,j-1],{j,1,Floor[n/2]}]],
    2])

del[x_Plus]       := PolynomialMod[del /@ x,2]
del[n_Integer x_] := PolynomialMod[del[x],2]
del[n_Integer]    := 0

del[x_lambda] :=
 Module[{lx},
  lx = Length[x];
  PolynomialMod[Sum[ o[x[[Range[i-1]]],dlambda[x[[i]]],x[[Range[i+1,lx]]]],{i,lx}],2]
 ]

del[ulambda[n_,i___]] := 
 del[lambda[i]] /. (lambda[j___] :> ulambda[n,j])

Basis[Lambda[0,0]] = {lambda[]}

Basis[Lambda[1,t_Integer]] :=
 (Basis[Lambda[1,t]] = If[t==0,{},{lambda[t-1]}])

Basis[Lambda[s_,t_]] := {} /; s<0 || t<0

Basis[Lambda[s_,t_]] :=
 (Basis[Lambda[s,t]] =
  Module[{r},
   Flatten[
     Table[
     Join[#,lambda[t-r-1]]& /@ 
      Select[Basis[Lambda[s-1,r]],2 Last[#] >= t-r-1&],
     {r,0,t-1}]]])

Basis[Lambda[n_,s_,t_]] := 
 (Basis[Lambda[n,s,t]] = 
   (Select[Basis[Lambda[s,t]],(Length[#] == 0 || First[#] < n) &]) /. 
       (lambda[i___] :> ulambda[n,i]) )

BL[a__] := Basis[Lambda[a]]

BasisFunction[V_][x_Plus] := BasisFunction[V] /@ x
BasisFunction[V_][0] := 0 Range[Length[Basis[V]]]
BasisFunction[V_][n_?EvenQ x_] := 0
BasisFunction[V_][n_?OddQ x_] := BasisFunction[V][x]

MakeBasisFunction[V_] := 
 Module[{B,d,id},
  B = Basis[V];
  d = Length[B];
  id = IdentityMatrix[d];
  Do[
   BasisFunction[V][B[[i]]] = id[[i]],
   {i,d}
  ]
 ]

Dim[V_] := Length[Basis[V]]

MapMatrix[f_,V_,W_] :=
 Module[{},
  MakeBasisFunction[W];
  BasisFunction[W] /@ f /@ Basis[V]
 ]

MapKernel[f_,V_,W_] := {} /; Dim[V] == 0
MapKernel[f_,V_,W_] := {} /; Dim[W] == 0

MapKernel[f_,V_,W_] :=
 (# . Basis[V]) & /@
   NullSpace[MapMatrix[f,V,W],Modulus -> 2] 

MapImage[f_,V_,W_] := {} /; Dim[V] == 0
MapImage[f_,V_,W_] := {} /; Dim[W] == 0

NonNull[v_] := Not[Equal @@ Join[{0},v]]

MapImage[f_,V_,W_] := 
 Module[{A}, 
  A = RowReduce[Transpose[MapMatrix[f,V,W]],Modulus -> 2];
  A = Select[A,NonNull];
  (# . Basis[W]) & /@ A
 ]

delKernel[s_,t_] := 
 MapKernel[del,Lambda[s,t],Lambda[s+1,t]]

delKernel[n_,s_,t_] := 
 MapKernel[del,Lambda[n,s,t],Lambda[n,s+1,t]]

delImage[s_,t_] := 
 MapImage[del,Lambda[s-1,t],Lambda[s,t]]
 
delImage[n_,s_,t_] := 
 MapImage[del,Lambda[n,s-1,t],Lambda[n,s,t]]

LambdaCanonical[x_Plus] := LambdaCanonical /@ x
LambdaCanonical[n_Integer x_] := If[EvenQ[n],0,LambdaCanonical[x]]

SplitLambda[n_,s_,t_] :=
 (SplitLambda[n,s,t] = 
  Module[{},
   d0 = MapMatrix[del,Lambda[n,s-1,t],Lambda[n,s,t]];
   d1 = MapMatrix[del,Lambda[n,s,t],Lambda[n,s+1,t]];
   BC = Basis[Lambda[n,s,t]];
   d = Length[BC];
   Ci = Range[d];
   B = 
    If[d0 == {},{},
     Select[RowReduce[d0,Modulus -> 2],NonNull]];
   BB = (# . BC) & /@ B;
   Bi = First[First[Position[#,1]]] & /@ B;
   Wi = Complement[Ci,Bi];
   BW = BC[[Wi]];
   H = 
    If[Wi == {}, {},
     If[Dim[Lambda[n,s+1,t]] == 0, IdentityMatrix[Length[Wi]],
     Reverse /@ NullSpace[Transpose[Reverse[d1[[Wi]]]], Modulus -> 2]]];
   BH = (# . BW) & /@ H;
   Hi = Wi[[ (First[First[Position[#,1]]] & /@ H) ]];
   Vi = Complement[Ci,Join[Bi,Hi]];
   BV = BC[[Vi]];
   Basis[LambdaBoundaries[n,s,t]] = BB;
   Basis[LambdaHomology[n,s,t]] = BH;
   Basis[LambdaNonBoundaries[n,s,t]] = BV;
   Do[
    x = BH[[i]];
    y = If[Head[x] === Plus,First[x],x];
    CurtisCycle[y] = x,
    {i,Length[BH]}
   ];
   M = Transpose[BasisFunction[Lambda[n,s,t]] /@ Join[BH,BB,BV]];
   Q = MapAt[0 # &,IdentityMatrix[Length[BC]],
	Table[{i},{i,Length[BH]+1,Length[BC]}]];
   P = Transpose[Mod[M.Q.Inverse[M,Modulus->2],2]];
   Do[
    LambdaCanonical[BC[[i]]] = P[[i]] . BC,
    {i,d}
   ]
  ];
  Null)

LambdaAssassin[0] = 0

LambdaAssassin[x_] :=
 Module[{},
  t = Tridegree[x];
  SplitLambda @@ t;
  src = Lambda @@ (t - {0,1,0});
  tgt = Lambda @@ t;
  v = BasisFunction[tgt][x];
  M = MapMatrix[del,src,tgt];
  Off[LinearSolve::nosol];
  u = LinearSolve[Transpose[M],v,Modulus -> 2];
  On[LinearSolve::nosol];
  If[Head[u] === LinearSolve,$Failed,u . Basis[src]]
 ]

MasseyProduct[x0_,x1_,x2_] := 
 Module[{x01,x12},
  x01 = LambdaAssassin[o[x0,x1]];
  x12 = LambdaAssassin[o[x1,x2]];
  LambdaCanonical[o[x01,Sigma[x2]] + o[x0,x12]]
 ]

(**********************************************************************)

LambdaRepresentative[0] = 0

LambdaRepresentative[x_Plus] := 
 LambdaRepresentative /@ x

LambdaRepresentative[x_o] := 
 LambdaRepresentative /@ x

LambdaRepresentative[n_Integer x_] :=
 Module[{m,y,i,q},
  y = LambdaRepresentative[x];
  m = n;
  While[EvenQ[m],
   y = y /. {lambda[i___] :> lambda[i,0],
             ulambda[q_,i___] :> ulambda[q,i,0]};
   m = m/2
  ];
  y
 ]

LambdaRepresentative[iota[n_]]  := ulambda[n]
LambdaRepresentative[eta[n_]]   := ulambda[n, 1] /; n >= 2
LambdaRepresentative[nu[n_]]    := ulambda[n, 3] /; n >= 4
LambdaRepresentative[sigma[n_]] := ulambda[n, 7] /; n >= 8

LambdaRepresentative[nuprime]  = ulambda[3, 2,1]

LambdaRepresentative[Sigma[nuprime]] = ulambda[4, 2,1]

LambdaRepresentative[sigmathird] =
  ulambda[5, 4,3,0,0] + ulambda[5, 3,2,2,0] + ulambda[5, 3,1,1,2]

LambdaRepresentative[sigmasecond] =
  ulambda[6, 3, 2, 2] + ulambda[6, 4, 3, 0] + ulambda[6, 5, 1, 1]

LambdaRepresentative[sigmaprime] =
  ulambda[7, 6,1] + ulambda[7, 4,3]

LambdaRepresentative[Sigma[sigmaprime]] =
  ulambda[8, 6,1] + ulambda[8, 4,3]


LambdaRepresentative[nubar[n_]] := ulambda[n, 5,3] /; n >= 6

LambdaRepresentative[epsilon[n_]] := 
 ulambda[n, 2,3,3] /; n >= 3

LambdaRepresentative[mu[n_]] :=
 ulambda[n, 1, 1, 2, 4, 1] +
 ulambda[n, 1, 2, 4, 1, 1] + 
 ulambda[n, 2, 1, 1, 2, 3] +
 ulambda[n, 2, 2, 2, 2, 1] + 
 ulambda[n, 2, 4, 1, 1, 1] /; n >= 3

LambdaRepresentative[epsilonprime] = 
 ulambda[3, 2, 3, 4, 1] + ulambda[3, 2, 4, 3, 1]

LambdaRepresentative[Sigma[epsilonprime]] =
 ulambda[4, 2, 3, 4, 1] + ulambda[4, 2, 4, 3, 1]

LambdaRepresentative[zeta[n_]] :=
 ulambda[n, 1, 1, 2, 4, 3] +
 ulambda[n, 2, 2, 2, 2, 3] + 
 ulambda[n, 2, 2, 4, 2, 1] +
 ulambda[n, 3, 1, 2, 4, 1] + 
 ulambda[n, 3, 2, 4, 1, 1] +
 ulambda[n, 3, 5, 1, 1, 1] + 
 ulambda[n, 4, 1, 1, 2, 3] +
 ulambda[n, 4, 2, 2, 2, 1] + 
 ulambda[n, 4, 4, 1, 1, 1] /; n >= 5

LambdaRepresentative[muprime] =
 ulambda[3, 1, 1, 2, 4, 2, 1] +
 ulambda[3, 1, 2, 4, 1, 2, 1] + 
 ulambda[3, 2, 1, 1, 2, 4, 1] +
 ulambda[3, 2, 1, 2, 4, 1, 1] + 
 ulambda[3, 2, 2, 2, 2, 2, 1] +
 ulambda[3, 2, 2, 4, 1, 1, 1] + 
 ulambda[3, 2, 4, 1, 1, 2, 1]

LambdaRepresentative[Sigma[muprime]] = 
 Sigma[LambdaRepresentative[muprime]]

LambdaRepresentative[theta] = 
 ulambda[12, 7, 5] + ulambda[12, 11, 1]

LambdaRepresentative[Sigma[theta]] = 
 Sigma[LambdaRepresentative[theta]]

LambdaRepresentative[thetaprime] =
 ulambda[11, 6, 5, 1] +
 ulambda[11, 7, 4, 1] + 
 ulambda[11, 10, 1, 1]

LambdaRepresentative[Sigma[thetaprime]] = 
 Sigma[LambdaRepresentative[thetaprime]]

LambdaRepresentative[o[nu[5],sigma[8]]] =
 ulambda[5, 4,3,3]

LambdaRepresentative[o[nu[n_],sigma[m_]]] :=
 ulambda[n, 4,3,3] /; n >= 5 && m === n+3

LambdaRepresentative[o[nu[n_],nu[m_],sigma[p_]]] := 
 ulambda[n, 3,4,3,3] /; m == n+3 && p == m+3 && n >= 4

LambdaRepresentative[o[nu[n_],sigma[m_],nu[p_]]] := 
 ulambda[n, 4,3,3,3] /; m == n+3 && p == m+7 && n >= 5

(* The following gives a generator in the right place in the *)
(* lambda algebra.  I do not know if it is compatible with   *)
(* Toda's definition as a Toda bracket.                      *)
LambdaRepresentative[kappa[n_]] := 
 ulambda[n, 3, 4, 4, 3] +
 ulambda[n, 3, 6, 2, 3] + 
 ulambda[n, 4, 7, 2, 1] +
 ulambda[n, 6, 2, 3, 3] /; n >= 5

LambdaRepresentative[epsilonbar[n_]] :=
 ulambda[n, 2, 3, 4, 3, 3] +
 ulambda[n, 2, 4, 3, 3, 3] /; n >= 3

LambdaRepresentative[rhofourth] = 
ulambda[5, 1, 1, 2, 4, 3, 1, 1, 2] + 
 ulambda[5, 1, 1, 2, 4, 3, 2, 2, 0] + 
 ulambda[5, 1, 1, 2, 4, 4, 3, 0, 0] + 
 ulambda[5, 1, 2, 4, 2, 3, 3, 0, 0] + 
 ulambda[5, 2, 2, 2, 2, 3, 1, 1, 2] + 
 ulambda[5, 2, 2, 2, 2, 3, 2, 2, 0] + 
 ulambda[5, 2, 2, 2, 2, 4, 3, 0, 0] + 
 ulambda[5, 2, 2, 4, 2, 1, 1, 1, 2] + 
 ulambda[5, 2, 2, 4, 2, 1, 2, 2, 0] + 
 ulambda[5, 2, 2, 4, 2, 2, 3, 0, 0] + 
 ulambda[5, 2, 4, 1, 2, 3, 3, 0, 0] + 
 ulambda[5, 3, 1, 2, 4, 1, 1, 1, 2] + 
 ulambda[5, 3, 1, 2, 4, 1, 2, 2, 0] + 
 ulambda[5, 3, 1, 2, 4, 2, 3, 0, 0] + 
 ulambda[5, 3, 2, 4, 1, 1, 1, 1, 2] + 
 ulambda[5, 3, 2, 4, 1, 1, 2, 2, 0] + 
 ulambda[5, 3, 2, 4, 1, 2, 3, 0, 0] + 
 ulambda[5, 3, 5, 1, 1, 1, 1, 1, 2] + 
 ulambda[5, 3, 5, 1, 1, 1, 2, 2, 0] + 
 ulambda[5, 3, 5, 1, 1, 2, 3, 0, 0] + 
 ulambda[5, 4, 1, 1, 2, 3, 1, 1, 2] + 
 ulambda[5, 4, 1, 1, 2, 3, 2, 2, 0] + 
 ulambda[5, 4, 1, 1, 2, 4, 3, 0, 0] + 
 ulambda[5, 4, 2, 2, 2, 1, 1, 1, 2] + 
 ulambda[5, 4, 2, 2, 2, 1, 2, 2, 0] + 
 ulambda[5, 4, 2, 2, 2, 2, 3, 0, 0] + 
 ulambda[5, 4, 4, 1, 1, 1, 1, 1, 2] + 
 ulambda[5, 4, 4, 1, 1, 1, 2, 2, 0] + 
 ulambda[5, 4, 4, 1, 1, 2, 3, 0, 0]

LambdaRepresentative[rhothird] = 
 ulambda[6, 1, 1, 2, 4, 4, 3, 0] + 
 ulambda[6, 1, 2, 3, 6, 2, 1, 0] + 
 ulambda[6, 1, 2, 4, 2, 3, 3, 0] + 
 ulambda[6, 2, 2, 2, 2, 4, 3, 0] + 
 ulambda[6, 2, 2, 4, 2, 2, 3, 0] + 
 ulambda[6, 2, 2, 4, 4, 2, 1, 0] + 
 ulambda[6, 2, 3, 5, 2, 2, 1, 0] + 
 ulambda[6, 2, 4, 1, 2, 3, 3, 0] + 
 ulambda[6, 2, 4, 6, 1, 1, 1, 0] + 
 ulambda[6, 3, 2, 2, 2, 2, 2, 2] + 
 ulambda[6, 3, 2, 2, 2, 4, 1, 1] + 
 ulambda[6, 3, 2, 2, 4, 1, 1, 2] + 
 ulambda[6, 3, 2, 4, 1, 1, 2, 2] + 
 ulambda[6, 3, 2, 4, 1, 2, 3, 0] + 
 ulambda[6, 3, 2, 4, 2, 2, 1, 1] + 
 ulambda[6, 3, 3, 6, 1, 1, 1, 0] + 
 ulambda[6, 3, 4, 1, 2, 4, 1, 0] + 
 ulambda[6, 3, 4, 2, 4, 1, 1, 0] + 
 ulambda[6, 3, 5, 1, 1, 2, 3, 0] + 
 ulambda[6, 3, 5, 2, 2, 2, 1, 0] + 
 ulambda[6, 3, 5, 2, 3, 1, 1, 0] + 
 ulambda[6, 3, 6, 3, 1, 1, 1, 0] + 
 ulambda[6, 4, 1, 1, 2, 4, 3, 0] + 
 ulambda[6, 4, 2, 2, 2, 2, 3, 0] + 
 ulambda[6, 4, 2, 2, 4, 2, 1, 0] + 
 ulambda[6, 4, 3, 1, 1, 2, 2, 2] + 
 ulambda[6, 4, 3, 1, 2, 3, 1, 1] + 
 ulambda[6, 4, 3, 1, 2, 4, 1, 0] + 
 ulambda[6, 4, 3, 2, 2, 1, 1, 2] + 
 ulambda[6, 4, 3, 2, 4, 1, 1, 0] + 
 ulambda[6, 4, 3, 4, 1, 2, 1, 0] + 
 ulambda[6, 4, 3, 5, 1, 1, 1, 0] + 
 ulambda[6, 4, 4, 1, 1, 2, 3, 0] + 
 ulambda[6, 4, 4, 2, 2, 2, 1, 0] + 
 ulambda[6, 4, 4, 3, 1, 2, 1, 0] + 
 ulambda[6, 4, 4, 4, 1, 1, 1, 0] + 
 ulambda[6, 4, 5, 1, 2, 2, 1, 0] + 
 ulambda[6, 4, 5, 3, 1, 1, 1, 0] + 
 ulambda[6, 4, 6, 2, 1, 1, 1, 0] + 
 ulambda[6, 5, 1, 1, 2, 2, 2, 2] + 
 ulambda[6, 5, 1, 1, 2, 4, 1, 1] + 
 ulambda[6, 5, 1, 2, 2, 2, 3, 0] + 
 ulambda[6, 5, 1, 2, 3, 1, 1, 2] + 
 ulambda[6, 5, 1, 2, 4, 2, 1, 0] + 
 ulambda[6, 5, 2, 2, 1, 1, 2, 2] + 
 ulambda[6, 5, 2, 2, 1, 2, 3, 0] + 
 ulambda[6, 5, 2, 2, 2, 2, 1, 1] + 
 ulambda[6, 5, 3, 4, 1, 1, 1, 0] + 
 ulambda[6, 5, 4, 1, 1, 2, 1, 1] + 
 ulambda[6, 5, 4, 3, 1, 1, 1, 0]

LambdaRepresentative[rhosecond] = 
ulambda[7, 1, 1, 2, 4, 4, 3] + 
 ulambda[7, 1, 2, 3, 6, 2, 1] + 
 ulambda[7, 1, 2, 4, 2, 3, 3] + 
 ulambda[7, 2, 2, 2, 2, 4, 3] + 
 ulambda[7, 2, 2, 4, 2, 2, 3] + 
 ulambda[7, 2, 2, 4, 4, 2, 1] + 
 ulambda[7, 2, 3, 5, 2, 2, 1] + 
 ulambda[7, 2, 4, 1, 2, 3, 3] + 
 ulambda[7, 2, 4, 6, 1, 1, 1] + 
 ulambda[7, 3, 3, 6, 1, 1, 1] + 
 ulambda[7, 3, 4, 1, 2, 4, 1] + 
 ulambda[7, 3, 4, 2, 4, 1, 1] + 
 ulambda[7, 3, 5, 1, 1, 2, 3] + 
 ulambda[7, 3, 5, 2, 2, 2, 1] + 
 ulambda[7, 3, 5, 2, 3, 1, 1] + 
 ulambda[7, 3, 6, 3, 1, 1, 1] + 
 ulambda[7, 4, 1, 1, 2, 4, 3] + 
 ulambda[7, 4, 2, 2, 2, 2, 3] + 
 ulambda[7, 4, 2, 2, 4, 2, 1] + 
 ulambda[7, 4, 3, 4, 1, 2, 1] + 
 ulambda[7, 4, 3, 5, 1, 1, 1] + 
 ulambda[7, 4, 4, 1, 1, 2, 3] + 
 ulambda[7, 4, 4, 2, 2, 2, 1] + 
 ulambda[7, 4, 4, 3, 1, 2, 1] + 
 ulambda[7, 4, 4, 4, 1, 1, 1] + 
 ulambda[7, 4, 5, 1, 2, 2, 1] + 
 ulambda[7, 4, 5, 3, 1, 1, 1] + 
 ulambda[7, 4, 6, 2, 1, 1, 1] + 
 ulambda[7, 5, 1, 2, 2, 2, 3] + 
 ulambda[7, 5, 1, 2, 4, 2, 1] + 
 ulambda[7, 6, 1, 1, 2, 4, 1] + 
 ulambda[7, 6, 1, 2, 4, 1, 1] + 
 ulambda[7, 6, 2, 1, 1, 2, 3] + 
 ulambda[7, 6, 2, 2, 2, 2, 1] + 
 ulambda[7, 6, 2, 4, 1, 1, 1] + 
 ulambda[7, 6, 3, 3, 1, 1, 1]

LambdaRepresentative[Sigma[rhosecond]] = 
 Sigma[LambdaRepresentative[rhosecond]]

LambdaRepresentative[rhoprime] = 
 ulambda[9, 3, 3, 6, 3, 0] + 
 ulambda[9, 3, 4, 4, 3, 1] + 
 ulambda[9, 3, 6, 2, 3, 1] + 
 ulambda[9, 4, 7, 2, 1, 1] + 
 ulambda[9, 5, 3, 6, 1, 0] + 
 ulambda[9, 5, 4, 2, 4, 0] + 
 ulambda[9, 5, 5, 2, 3, 0] + 
 ulambda[9, 6, 2, 3, 3, 1] + 
 ulambda[9, 6, 3, 2, 4, 0] + 
 ulambda[9, 6, 5, 2, 2, 0] + 
 ulambda[9, 6, 5, 4, 0, 0] + 
 ulambda[9, 6, 6, 2, 1, 0] + 
 ulambda[9, 7, 1, 1, 2, 4] + 
 ulambda[9, 7, 1, 2, 4, 1] + 
 ulambda[9, 7, 2, 2, 2, 2] + 
 ulambda[9, 7, 2, 2, 4, 0] + 
 ulambda[9, 7, 2, 4, 1, 1] + 
 ulambda[9, 7, 3, 5, 0, 0] + 
 ulambda[9, 7, 4, 1, 1, 2] + 
 ulambda[9, 7, 4, 2, 2, 0] + 
 ulambda[9, 7, 4, 4, 0, 0] + 
 ulambda[9, 7, 5, 1, 2, 0] + 
 ulambda[9, 7, 6, 2, 0, 0] + 
 ulambda[9, 8, 7, 0, 0, 0]

LambdaRepresentative[Sigma[rhoprime]] = 
 ulambda[10, 3, 3, 6, 3, 0] + 
 ulambda[10, 3, 6, 6, 0, 0] + 
 ulambda[10, 5, 4, 2, 2, 2] + 
 ulambda[10, 5, 4, 4, 1, 1] + 
 ulambda[10, 5, 5, 2, 3, 0] + 
 ulambda[10, 5, 5, 5, 0, 0] + 
 ulambda[10, 5, 7, 3, 0, 0] + 
 ulambda[10, 5, 8, 2, 0, 0] + 
 ulambda[10, 5, 9, 1, 0, 0] + 
 ulambda[10, 6, 3, 2, 2, 2] + 
 ulambda[10, 6, 3, 4, 1, 1] + 
 ulambda[10, 6, 5, 1, 1, 2] + 
 ulambda[10, 6, 6, 2, 1, 0] + 
 ulambda[10, 6, 7, 2, 0, 0] + 
 ulambda[10, 6, 9, 0, 0, 0] + 
 ulambda[10, 7, 2, 2, 2, 2] + 
 ulambda[10, 7, 2, 2, 4, 0] + 
 ulambda[10, 7, 2, 4, 1, 1] + 
 ulambda[10, 7, 3, 5, 0, 0] + 
 ulambda[10, 7, 4, 1, 1, 2] + 
 ulambda[10, 7, 4, 2, 2, 0] + 
 ulambda[10, 7, 4, 4, 0, 0] + 
 ulambda[10, 7, 5, 1, 2, 0] + 
 ulambda[10, 7, 6, 2, 0, 0] + 
 ulambda[10, 8, 7, 0, 0, 0] + 
 ulambda[10, 9, 1, 1, 2, 2] + 
 ulambda[10, 9, 1, 2, 3, 0] + 
 ulambda[10, 9, 2, 2, 1, 1] + 
 ulambda[10, 9, 3, 1, 1, 1] + 
 ulambda[10, 9, 3, 2, 1, 0] + 
 ulambda[10, 9, 3, 3, 0, 0]

LambdaRepresentative[Sigma[Sigma[rhoprime]]] = 
 ulambda[11, 6, 5, 1, 1, 2] + 
 ulambda[11, 6, 5, 2, 2, 0] + 
 ulambda[11, 6, 5, 4, 0, 0] + 
 ulambda[11, 7, 3, 5, 0, 0] + 
 ulambda[11, 7, 4, 1, 1, 2] + 
 ulambda[11, 7, 4, 2, 2, 0] + 
 ulambda[11, 7, 4, 4, 0, 0] + 
 ulambda[11, 7, 5, 1, 2, 0] + 
 ulambda[11, 7, 6, 2, 0, 0] + 
 ulambda[11, 8, 7, 0, 0, 0] + 
 ulambda[11, 10, 1, 1, 1, 2] + 
 ulambda[11, 10, 1, 2, 2, 0] + 
 ulambda[11, 10, 2, 3, 0, 0]

LambdaRepresentative[Sigma[Sigma[Sigma[rhoprime]]]] = 
 ulambda[12, 6, 5, 1, 1, 2] + 
 ulambda[12, 6, 5, 2, 2, 0] + 
 ulambda[12, 6, 5, 4, 0, 0] + 
 ulambda[12, 7, 4, 1, 1, 2] + 
 ulambda[12, 7, 4, 2, 2, 0] + 
 ulambda[12, 7, 4, 4, 0, 0] + 
 ulambda[12, 7, 5, 1, 2, 0] + 
 ulambda[12, 7, 6, 2, 0, 0] + 
 ulambda[12, 8, 7, 0, 0, 0] + 
 ulambda[12, 10, 1, 1, 1, 2] + 
 ulambda[12, 10, 1, 2, 2, 0] + 
 ulambda[12, 10, 2, 3, 0, 0] + 
 ulambda[12, 11, 3, 1, 0, 0]

LambdaRepresentative[rho[n_]] := 
 ulambda[n, 7, 5, 1, 2] +
 ulambda[n, 7, 6, 2, 0] + 
 ulambda[n, 8, 7, 0, 0] +
 ulambda[n, 11, 1, 1, 2] + 
 ulambda[n, 11, 2, 2, 0] +
 ulambda[n, 12, 3, 0, 0] /; n >= 13

LambdaRepresentative[zetaprime] = 
 ulambda[6, 3, 3, 5, 1, 2, 2] + 
 ulambda[6, 3, 3, 5, 2, 3, 0] + 
 ulambda[6, 3, 4, 6, 1, 1, 1] + 
 ulambda[6, 3, 5, 4, 4, 0, 0] + 
 ulambda[6, 3, 6, 3, 4, 0, 0] + 
 ulambda[6, 3, 6, 6, 1, 0, 0] + 
 ulambda[6, 3, 6, 7, 0, 0, 0] + 
 ulambda[6, 4, 3, 3, 4, 1, 1] + 
 ulambda[6, 4, 3, 6, 1, 1, 1] + 
 ulambda[6, 4, 7, 5, 0, 0, 0] + 
 ulambda[6, 5, 3, 2, 2, 2, 2] + 
 ulambda[6, 5, 3, 2, 2, 4, 0] + 
 ulambda[6, 5, 3, 4, 1, 1, 2] + 
 ulambda[6, 5, 3, 4, 2, 2, 0] + 
 ulambda[6, 5, 3, 4, 4, 0, 0] + 
 ulambda[6, 5, 3, 5, 1, 2, 0] + 
 ulambda[6, 5, 3, 6, 2, 0, 0] + 
 ulambda[6, 5, 4, 7, 0, 0, 0] + 
 ulambda[6, 5, 5, 1, 1, 2, 2] + 
 ulambda[6, 5, 5, 1, 2, 3, 0] + 
 ulambda[6, 5, 5, 3, 1, 1, 1] + 
 ulambda[6, 5, 5, 5, 1, 0, 0] + 
 ulambda[6, 5, 6, 2, 1, 1, 1] + 
 ulambda[6, 5, 6, 5, 0, 0, 0] + 
 ulambda[6, 5, 7, 2, 2, 0, 0] + 
 ulambda[6, 5, 9, 1, 1, 0, 0] + 
 ulambda[6, 5, 10, 1, 0, 0, 0]

LambdaRepresentative[Sigma[zetaprime]] = 
 ulambda[7, 4, 3, 3, 4, 1, 1] + 
 ulambda[7, 4, 3, 6, 1, 1, 1] + 
 ulambda[7, 6, 3, 4, 1, 1, 1] + 
 ulambda[7, 6, 4, 3, 1, 1, 1]

LambdaRepresentative[Sigma[Sigma[zetaprime]]] = 
 Sigma[LambdaRepresentative[Sigma[zetaprime]]]

LambdaRepresentative[omega[n_]] := 
 ulambda[n, 9, 7] + ulambda[n, 13, 3] /; n >= 14

LambdaRepresentative[etastarprime] =
 ulambda[15, 8, 7, 1] + ulambda[15, 12, 3, 1] + ulambda[15, 14, 1, 1]

LambdaRepresentative[Sigma[etastarprime]] = 
 Sigma[LambdaRepresentative[etastarprime]]

LambdaRepresentative[etastar[n_]] :=
 ulambda[n, 15, 1] /; n >= 16

LambdaRepresentative[epsilonbarprime] =
 ulambda[3, 2, 3, 4, 3, 4, 1] +
 ulambda[3, 2, 3, 4, 4, 3, 1] + 
 ulambda[3, 2, 4, 3, 3, 4, 1] +
 ulambda[3, 2, 4, 3, 4, 3, 1]

LambdaRepresentative[Sigma[epsilonbarprime]] = 
 Sigma[LambdaRepresentative[epsilonbarprime]]

LambdaRepresentative[w[n_]] := 
 del[lambda[n]] /. (lambda[j___] :> ulambda[n,j])


 










LambdaWitness[2 eta[3]] = ulambda[3, 2]

LambdaWitness[8 nu[5]] = ulambda[7, 4,0,0] + ulambda[7, 2,2,0] + ulambda[7, 1,1,2]

LambdaWitness[Hopf[o[nuprime,eta[6],eta[7]]] - 4 nu[5]] =
 ulambda[5, 4,0]

LambdaWitness[Hopf[o[sigmaprime, eta[14], eta[15]]] - 4 nu[13]] = 
 ulambda[13, 2, 2] + ulambda[13, 4, 0]







AdamsDifferential[2,lambda[i_]] := lambda[i-1,i-1,0] /; i >= 4











Null;

