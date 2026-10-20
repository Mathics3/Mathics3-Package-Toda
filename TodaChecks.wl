MaxStem = 19

ImageList[f_,k_,l_] :=
 Select[Zap[f /@ Generators[SpherePi[k,l]]],
        # =!= 0 &] /. _Integer x_ :> x

SubsetQ[S_,T_] := (Complement[S,T] === {})

stemsort[l_] := 
 Module[{m},
  m = {#[[1]]-#[[2]],#[[1]],#[[2]]} & /@ l;
  m = Sort[m];
  m = Drop[#,1] & /@ m; 
  m
 ]
 
CheckSigma[k_,l_] :=
 ElementQ[ImageList[Sigma,k,l], SpherePi[k+1,l+1]]

CheckHopf[k_,l_] :=
 ElementQ[ImageList[Hopf,k,l], SpherePi[k,2l-1]]

CheckWhiteheadP[k_,l_?OddQ] := 
 ElementQ[ImageList[WhiteheadP,k,l], SpherePi[k-2,(l-1)/2]]

SigmaCheckList =
 Flatten[Table[{k,m},{m,1,MaxStem+2},{k,1,m+MaxStem}],1]

CheckSigmaAll := 
 stemsort[Select[SigmaCheckList,Not[CheckSigma @@ #] &]]

HopfCheckList =  Flatten[Table[{k,n},{n,1,MaxStem+1},{k,1,n+MaxStem}],1]

CheckHopfAll := 
 stemsort[Select[HopfCheckList,Not[CheckHopf @@ #] &]]

WhiteheadPCheckList =
 Flatten[Table[{k,2n+1},{n,0,Floor[(MaxStem-1)/2]},{k,3,n+MaxStem+2}],1]

CheckWhiteheadPAll := 
 stemsort[Select[WhiteheadPCheckList,Not[CheckWhiteheadP @@ #] &]]

CheckHE[k_,n_] :=
 Module[{gens,Egens,HEgens},
  gens = Generators[SpherePi[k,n]];
  Egens = Zap[Sigma /@ gens];
  HEgens = Zap[Hopf /@ Egens];
  Union[HEgens,{0}] === {0}
 ]

CheckHEAll := 
 stemsort[Select[SigmaCheckList,Not[CheckHE @@ #] &]]

CheckPH[k_,n_] :=
 Module[{gens,Hgens,PHgens},
  gens = Generators[SpherePi[k,n]];
  Hgens = Zap[Hopf /@ gens];
  PHgens = Zap[WhiteheadP /@ Hgens];
  Union[PHgens,{0}] === {0}
 ]

CheckPHAll := 
 stemsort[Select[HopfCheckList,Not[CheckPH @@ #] &]]

CheckEP[k_,n_?OddQ] :=
 Module[{gens,Pgens,EPgens},
  gens = Generators[SpherePi[k,n]];
  Pgens = Zap[WhiteheadP /@ gens];
  EPgens = Zap[Sigma /@ Pgens];
  Union[EPgens,{0}] === {0}
 ]

CheckEPAll := 
 stemsort[Select[WhiteheadPCheckList,Not[CheckEP @@ #] &]]

CheckComp[p_,q_,r_] := 
 ElementQ[
  Zap[Flatten[
   Outer[o,
    Generators[SpherePi[q,r]],
    Generators[SpherePi[p,q]]
   ]]],
  SpherePi[p,r]]

ShowCheckComp[p_,q_,r_] := 
 Module[{elts,tgt},
  elts =
  Zap[Flatten[
   Outer[o,
    Generators[SpherePi[q,r]],
    Generators[SpherePi[p,q]]
   ]]];
  tgt = SpherePi[p,r];
  elts = Select[elts,Not[ElementQ[#,tgt]]&];
  {{p,q,r},tgt,elts}
 ]


CompCheckList = 
 Flatten[
  Table[{i,j,k},{k,1,12},{j,k,k+11},{i,j,k+11}],2]

CheckCompAll := 
 Select[CompCheckList,Not[CheckComp @@ #] &]

badcomp := (ShowCheckComp @@ # &) /@  CheckCompAll





Subsets[0] = {{}}

Subsets[n_Integer] :=
 (Subsets[n] = 
   Join[Subsets[n - 1], Join[#, {n}] & /@ Subsets[n - 1]])

Subsets[S_List] := S[[#]] & /@ Subsets[Length[S]]

Locate[u_,verbose_:True] :=
 Module[{good},
(* {src,tgt,home,elts,good,criteria,critsets,mincrit,Ex,Hx,Px}, *)
  x = u;
  src = SourceSphere[x];
  tgt = TargetSphere[x];
  home = SpherePi[src,tgt];
  gens = Generators[home];
  elts = Elements[home];
  xx = Zap[x];
  If[MemberQ[elts,xx],
   If[xx === x,
    Print[
     SequenceForm[
      x,
      " is visibly an integral combination of the standard generators ",
      " of the group ", 
      Subsuperscript["\[Pi]",src,tgt]," = ",home
     ]
    ],
    Print[
     SequenceForm[
      x," = ",xx,
      " is an integral combination of the standard generators ",
      " of the group ", 
      Subsuperscript["\[Pi]",src,tgt]," = ",home
     ]
    ]
   ];
   Return[{xx}]
  ];
  criteria = {};
  good[{}] = elts;
  Ex = Zap[Sigma[x]];
  Etgt = SpherePi[src+1,tgt+1];
  If[Head[Etgt] == Group && ElementQ[Ex,Etgt] &&
     And @@ (ElementQ[Zap[Sigma[#]],Etgt] & /@ gens),
   criteria = Join[criteria,{Sigma}];
   good[{Sigma}] = Select[elts,Zap[Sigma[#]] == Ex &]
  ];
  Htgt = SpherePi[src,2 tgt - 1];
  Hx = Zap[Hopf[x]];
  If[Head[Htgt] == Group && ElementQ[Hx,Htgt] &&
     And @@ (ElementQ[Zap[Hopf[#]],Htgt] & /@ gens),
   criteria = Join[criteria,{Hopf}];
   good[{Hopf}] = Select[elts,Zap[Hopf[#]] == Hx &]
  ];
  If[OddQ[tgt],
   Ptgt = SpherePi[src-2,(tgt-1)/2];
   Px = Zap[WhiteheadP[x]];
   If[Head[Ptgt] == Group && ElementQ[Px,Ptgt] &&
     And @@ (ElementQ[Zap[WhiteheadP[#]],Ptgt] & /@ gens),
    criteria = Join[criteria,{WhiteheadP}];
    good[{WhiteheadP}] = Select[elts,Zap[WhiteheadP[#]] == Px &]
   ]
  ];
  critsets = Sort[Subsets[criteria],Length[#1] < Length[#2] &];
  setgood[A_] := (Evaluate[good[A]] = Intersection @@ (good[{#}]& /@ A));
  setgood /@ Select[critsets,Length[#] > 1 &];
  gd = good;
  mincrit = Min @@ (Length /@ good /@ critsets);
  minset = First[Select[critsets,Length[good[#]] == mincrit &]];
  If[Length[good[minset]] === Length[elts],
   Print[SequenceForm[
    x,"\[Element]",Subsuperscript["\[Pi]",src,tgt]," = ",
    Format[home],"\n",
    "No additional information was found."
   ]];
   Return[good[minset]]
  ];
  Print[SequenceForm[x,"\[Element]",good[minset]]];
  Print[ShowMap[#,x]] & /@ minset;
  Return[good[minset]]
 ]

allgens = Flatten[Table[Generators[SpherePi[n + k, n]], {n, 20}, {k, 19}]]

SigmaOK[a_] := 
 Module[{b},
  b = Zap[Sigma[a]];
  ElementQ[b,Home[b]]
 ]

HopfOK[a_] := 
 Module[{b},
  b = Zap[Hopf[a]];
  ElementQ[b,Home[b]]
 ]

WhiteheadPOK[a_] := 
 Module[{b},
  If[EvenQ[TargetSphere[b]],Return[True]];
  b = Zap[WhiteheadP[a]];
  ElementQ[b,Home[b]]
 ]

badSigma := Sort[Select[allgens, Not[SigmaOK[#]] &], Stem[#1] < Stem[#2] &]
badHopf  := Sort[Select[allgens, Not[HopfOK[#]] &], Stem[#1] < Stem[#2] &]
badWhiteheadP := 
 Sort[Select[allgens, Not[WhiteheadPOK[#]] &], Stem[#1] < Stem[#2] &]

LR = LambdaRepresentative
LC = LambdaCanonical
LL[t_] := LC[LR[t]]
