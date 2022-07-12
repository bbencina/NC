(*  NCPolyGroebner.m                                                       *)
(*  Author: Mauricio de Oliveira                                           *)
(*    Date: July 2009                                                      *)
(* Version: 0.1 ( initial implementation )                                 *)

BeginPackage[ "NCPolyGroebner`",
              "NCPoly`"  ];

Clear[NCPolyGroebner,
      VerboseLevel,
      PrintBasis, 
      PrintObstructions, 
      PrintSPolynomials, 
      SimplifyObstructions,
      ReduceBasis,
      CleanUpBasis,
      SortObstructions,
      SortBasis
     ];
Options[NCPolyGroebner] = {
  VerboseLevel -> 1,
  PrintBasis -> False,
  PrintObstructions -> False,
  PrintSPolynomials -> False,
  SimplifyObstructions -> True,
  ReduceBasis -> True,
  CleanUpBasis -> False,
  SortObstructions -> False,
  SortBasis -> False,
  RemoveRedundant -> False,
  Labels -> {}
};

Get["NCPolyGroebner.usage", CharacterEncoding->"UTF8"];

NCPolyGroebner::Interrupted = "Stopped trying to find a Groebner basis at `1` polynomials";

Begin["`Private`"];

(* Other operations *)
Clear[NCPolySFactorExpand];
NCPolySFactorExpand[s_List, p1_NCPoly, p2_NCPoly] := 
  MapThread[NCPolyQuotientExpand[{#1},#2]&, {s, {p1, p2}}];

(* S-Polynomial matches *)
Clear[NCPolySFactors];
NCPolySFactors[r_NCPoly, s_NCPoly] := Block[
  { n = r[[1]] },

  Return[ 
    Map[ NCPolyMonomial[#, n]&
        ,
         NCPadAndMatch[
           NCIntegerDigits[Part[NCPolyLeadingTerm[r], 1], n],
           NCIntegerDigits[Part[NCPolyLeadingTerm[s], 1], n]
         ]
        ,
         {3} 
       ]
  ];
] /; NCPolyNumberOfVariables[r] === NCPolyNumberOfVariables[s];


(* Utilities *)

Clear[NCPolyGroebnerObstructions];
NCPolyGroebnerObstructions[G_List, j_Integer, simplify_] := Block[
  { i, OBS = {}, OBSi, d },

  (* Compute new set of obstructions *)
  For[ i = 1, i <= j, i++,

       (* Compute matches *)
       OBSi = NCPolySFactors[G[[i]], G[[j]]];

       (* Print["TEST**** OBSi = ", OBSi]; *)

       (* Compute degree *)
       d = NCPolyDegree[G[[j]]];

       If[ OBSi =!= {},
           (* compute sugar *)
           d += Apply[Plus, Map[NCPolyDegree, OBSi[[All, 2]], {2}], {1}];

 	   (* add to OBS *)
           (* OBS = Join[OBS, Map[{{i, j}, #}&, OBSi]]; *)
           OBS = Join[OBS, MapThread[{{i, j}, #1, #2}&, {OBSi, d}]];
       ];
  ];

  Return[OBS];

];

Clear[NCPolyGroebnerSimplifyObstructions];
NCPolyGroebnerSimplifyObstructions[OBSs_List, TG_List, m_Integer, verboseLevel_Integer] := Block[
  { tt, n, l, i, ij, jj, tk, ltkr, match, k, OBS = OBSs },

  (* ATTENTION: TG is list with leading monomials only! *)

  (* Simplify OBS(i) for all i < m  *)
 
  (* get leading term of the mth polynomial *)
  tt = TG[[m]];
  n = NCPolyNumberOfVariables[tt];
  (* Print["tt = ", NCPolyDisplay[tt]]; *)

  l = Length[OBS];
  For[ i = 1, i <= l, i++,

       ij = Part[OBS, i, 1];
       jj = Part[ij, 2]; 
       OBSij = Part[OBS, i, 2, 2];

       (* Print["ij = ", ij];
	Print["OBSij = ", OBSij]; *)

       If[ jj >= m,
           (* All remaining obstructions have i >= m *)
           Print["* All remaining obstructions have i >= m"];
           Break[];
       ];

       (* get leading term of the jth polynomial *)
       tk = TG[[jj]];
       (* Print["tk = ", NCPolyDisplay[tk]]; *)

       (* compute expanded monomial ltkr = l tk r *)
       ltkr = NCPolyQuotientExpand[{OBSij}, tk];
       (* Print["ltkr = ", NCPolyDisplay[ltkr]]; *)

       (* try match with right and left sides different than 1 *)
       match = MatchQ[
		  NCIntegerDigits[Part[NCPolyLeadingTerm[ltkr], 1], n],
                  Join[{l__}, NCIntegerDigits[Part[NCPolyLeadingTerm[tt], 1], n], {r__}]
		]; 
       (* Print["match = ", match]; *)

       If[ match === True,

           If[ verboseLevel >= 3,  
               Print[ "* Removing obstructions (", 
                      ToString[ij], ") ",
                      "from set of obstructions" ];
           ];

           (* Remove obstructions from OBS *)
           OBS = Delete[OBS, i];
           i--; l--;

           (* Print["> ", Map[ColumnForm,{OBS[[All,1]], Map[NCPolyDisplay, Map[Rest, OBS], {4}]}]]; *)

       ];
   ];

  Return[OBS];

];

(* F4 selection function *)
Clear[SelectionFunction];
SelectionFunction[obs_] := Module[
    {OBS=obs, mindeg, mindegOBS},
    (* get minimal degree *)
    mindeg = Min[OBS[[All,3]]];
    (* filter obstructions *)
    mindegOBS = Select[OBS, #[[3]] == mindeg &];
    If[ verboseLevel >= 3,
        Print["> mindegOBS = ", Map[ColumnForm,{mindegOBS[[All,1]], Map[NCPolyDisplay[#, labels]&, Map[Part[#, 2]&, mindegOBS], {3}], mindegOBS[[All,3]]}]];
    ];
    Return[mindegOBS];
];

(* helper function for the algorithm *)

(* actually get MONIC monomials *)
Clear[GetMonomials];
GetMonomials[L_List] := Module[
    {F = L, Mon},

    Mon = Flatten[Map[NCPolyToList, F]];
    Mon = Select[Mon, Not[#[[2, 1]] == 0]&];
    Mon = DeleteDuplicates[Map[NCPolyNormalize, Mon]];
    Return[Mon];
];

(* actually get MONIC leading monomials *)
Clear[GetLeadingMonomials];
GetLeadingMonomials[L_List] := Module[
    {F = L, Mon},

    Mon = Map[NCPolyLeadingMonomial, F];
    Mon = Select[Mon, Not[#[[2, 1]] == 0]&];
    Mon = DeleteDuplicates[Map[NCPolyNormalize, Mon]];
    Return[Complement[Mon,{0}]];
];

(* helper function for NCPolyF4SymbolicPreprocessing *)
(*
    NCPolyGetDivisors checks whether any of the polynomials in G lead reduces
the monomial m, as in Faugere's F4 paper, SymbolicPreprocessing, if-condition.
*)
Clear[NCPolyGetDivisors];
NCPolyGetDivisors[G_List, m_NCPoly] := Module[
    {i, OBSi = {}, OBS = {}, d, DIV = {}},

    For[i = 1, i <= Length[G], i++,
        (* obtain possible divisor combinations *)
        OBSi = NCPolySFactors[G[[i]], m];
        d = NCPolyDegree[m];
        If[OBSi =!= {},
            d += Apply[Plus, Map[NCPolyDegree, OBSi[[All, 2]], {2}], {1}];
            (* assemble divisor combinations *)
            OBS = MapThread[{{i, Length[G] + 1}, #1, #2} &, {OBSi, d}];
            (* the divisors are really just the second entry *)
            OBS = OBS[[All, 2]];
            (* construct the product polynomials lgr (and m) *)
            OBS = Map[NCPolySFactorExpand[#, G[[i]], m] &, OBS];
            (* take only those that don't change m, i.e. m = lgr, not some multiple *)
            OBS = Select[OBS, #[[2]] - m == 0 &];
            (* the order of arguments in NCPolySFactors implies lgr is the first element *)
            OBS = OBS[[All, 1]];
            (* add to set *)
            DIV = Join[DIV, OBS];
        ];
    ];
   Return[DIV];
];

(* F4 algo - SymbolicPreprocessing *)
(*
    A non-commutative version of the SymbolicPreprocessing functions from
Faugere's original F4 paper.
*)
Clear[NCPolyF4SymbolicPreprocessing];
NCPolyF4SymbolicPreprocessing[L_List, g_List] := Module[
    {F = L, G = g, Don, Mon, maxdeg, m, mDiv},

    (* obtain the monomials with coef 1 *)
    Mon = GetMonomials[F];
    (* Done set = leading monomials *)
    Don = GetLeadingMonomials[F];
    Mon = Complement[Mon, Don];
    While[Complement[Mon, Don] =!= {},
        (* get a monomials with the largest degree (just the first one) *)
        maxdeg = Max[Map[NCPolyDegree, Mon]];
        m = Select[Mon, NCPolyDegree[#] == maxdeg &][[1]];
        (* mark it Done *)
        Don = Join[Don, {m}];
        Mon = Complement[Mon, {m}];
        (* check whether m = lgr for g in G and add these *)
        mDiv = NCPolyGetDivisors[G, m];
        F = Join[F, mDiv];
    ];
    F = DeleteDuplicates[F];
    Return[F];
];

(* helper function for NCPolyF4Reduction *)
(*
    This function assembles polynomials into a matrix of coefficients, applies
the Gauss Reduced Row Echelon Form algorithm, then collects the new
polynomials.
*)
Clear[NCPolyRowEchelonForm];
NCPolyRowEchelonForm[L_List] := Module[
    {F = L, Mon, sMon, Mat, rMat, nPol, ms},

    (* obtain monomials with coef 1 *)
    Mon = GetMonomials[F];
    (* sort them - so that RowReduce operates wrt the monomial order > *)
    sMon = Reverse[Sort[Mon]];
    (* assemble the polynomials into matrix rows wrt sMon with coefficients as entries *)
    Mat = Table[Map[NCPolyCoefficient[F[[i]], #] &, sMon], {i, Length[F]}];
    (* just the regular row reduce *)
    rMat = RowReduce[Mat];
    (* collect the new polynomials *)
    nPol = Table[Dot[rMat[[i]], sMon], {i, Length[rMat]}];
    (* since we use table (much faster than 2 for-loops, we have to remove all the zero rows -> zero polynomials *)
    Return[Complement[nPol, {0}]];
];

(* F4 algo - Reduction *)
(*
    A non-commutative version of the Reduction functions from Faugere's
original F4 paper.
*)
Clear[NCPolyF4Reduction];
NCPolyF4Reduction[L_List, g_List] := Module[
    {F = L, G = g, SPF, rSPF, LM, rSPFPlus},

    (* apply SymbolicPreprocessing to obtain possible new polynomials for row reduction *)
    SPF = NCPolyF4SymbolicPreprocessing[F, G];
    (* do the row reduction *)
    rSPF = NCPolyRowEchelonForm[SPF];
    (* leading monomials *)
    LM = GetLeadingMonomials[SPF];
    (* collect those polynomials from reduction whose leading monomial is not already in the existing set *)
    rSPFPlus = Select[rSPF, Not[MemberQ[LM, NCPolyLeadingMonomial[#]]] &];
    Return[rSPFPlus];
];

(* Add to basis *)
Clear[AddToBasis];
AddToBasis[g_, tg_, obs_, 
           gnodes_, gtree_,
           h_, ij_,
           labels_, simplifyOBS_, verboseLevel_] := Module[
  {G,TG,OBS,m,GNodes,GTree,node},
         
  (* Normalize and add h to G, TG *)
  G = Append[g, NCPolyNormalize[h]];
  TG = Append[tg, NCPolyLeadingMonomial[Last[G]]];
  m = Length[G];

  If[ verboseLevel >= 3,
      Print["* S-Polynomial added to current basis"];
  ];
               
  (* Update tree *)
  GNodes = Append[gnodes, m];
  GTree = VertexAdd[gtree, m];
  GTree = EdgeAdd[GTree, Thread[Union[ij] -> m]];
               
  If[ verboseLevel >= 3,
      Print["* Added node to GTree"];
      If[ verboseLevel >= 4,
          Print["* GTree = ", 
                Graph[VertexReplace[GTree, 
                                    Thread[GNodes -> NCPolyDisplay[G]]], 
                      VertexLabels -> "Name"]];
          Print["* GNodes = ", GNodes];
          Print["* Acyclic? = ", AcyclicGraphQ[GTree]];
          If[ verboseLevel >= 5,
              Print["* ij = ", ij];
          ];
      ];
  ];
               
  If[ simplifyOBS,
    If[ verboseLevel >= 3,
        Print["* Simplify current set of obstructions"];
    ];
    OBS = NCPolyGroebnerSimplifyObstructions[obs, TG, m, verboseLevel];
  ];

  If[ verboseLevel >= 3,
      Print["* Computing new set of obstructions"];
  ];

  (* add new obstructions *)
  OBS = Join[OBS, NCPolyGroebnerObstructions[G, m, simplifyOBS]];

  If[ printObstructions, 
      Print["* New set of obstructions:"];
      Print["> OBS = ", Map[ColumnForm,{OBS[[All,1]], Map[NCPolyDisplay[#,labels]&, Map[Part[#, 2]&, OBS], {3}], OBS[[All,3]]}]];
  ];
    
  Return[{G,TG,OBS,m,GNodes,GTree}];
               
];
        
Clear[ReducePolynomial];
ReducePolynomial[G_,H_,labels_,
                 symbolicCoefficients_, 
                 verboseLevel_, complete_:False] := Module[
  {q,h = H,ij = {}},

  q = {1};
  While[ And[ h =!= 0, Flatten[q] =!= {}], 

         (* Reduce *)
         {q, h} = NCPolyReduceWithQuotient[h, G, Complete->complete];
         
         (* Collect contributions *)
         If[ q =!= {}, ij = Union[ij, Part[q, All, 2]] ];
         
         (* Make sure to simplify coefficients in case of
            symbolic coefficients *)
         If[ h =!= 0 && symbolicCoefficients,
             h = NCPolyPack[NCPolyTogether[h]];
         ];
         
         If[ verboseLevel >= 5,
             Print["> ij = ", ij];
             Print["> h = ", NCPolyDisplay[h, labels]];
             Print["> q = ", Map[NCPolyDisplay[#,labels]&, q, {4}]];
             (* Print["> G = ", Map[NCPolyDisplay[#,labels]&, G]]; *)
         ];
  ];
  
  Return[{h, ij}];
];

Clear[DoReduceBasis];
DoReduceBasis[{g__NCPoly}, 
              graph_, gnodes_,
              symbolicCoefficients_, 
              verboseLevel_, 
              complete_:False] := Block[
  { r = {g}, GTree = graph, GNodes = gnodes,
    m, ri, rii, ii, ij, modified = False, 
    index, rule },

  m = Length[r];
  If[ m > 1,
    For [ii = 1, ii <= m, ii++, 

      If[ verboseLevel >= 3,
          Print["* Cleaning up ", ii , "th basis entry"];
      ];
         
      rii = r[[ii]];
      {ri, ij} = ReducePolynomial[Delete[r, ii], rii,
                                  symbolicCoefficients,
                                  verboseLevel, 
                                  complete];

      (* Continue if nothing changed... *)
      If [ ri === rii,
           Continue[];
      ];
         
      (* Build reduced index *)
      index = Insert[Range[m-1], 0, ii];

      (* Make node ii be -1 and adjust other nodes *)
      rule = Append[
        Thread[Delete[GNodes, ii] -> Delete[index, ii]],
        GNodes[[ii]] -> -1
      ];
      GTree = VertexReplace[GTree, rule];

      (* Replace edges containing -1 
         by edges containing ij *)
      GTree = EdgeAdd[GTree, 
        Complement[
          Flatten[EdgeList[GTree, 
                           DirectedEdge[-1, 
                                        Except[Alternatives @@ ij]]]
                             /. Map[List, Thread[-1 -> ij]]]
         ,
          EdgeList[GTree, DirectedEdge[Alternatives @@ ij, _]]
        ]
      ];
                    
      (* Add node 0 to ij? *)
      If[ EdgeQ[GTree, 0 -> -1],
          If[ verboseLevel >= 3,
              Print["* Node contains 0"];
          ];
          AppendTo[ij, 0];
      ];
         
      (* Remove element -1 from GTree *)
      GTree = VertexDelete[GTree, -1];
      GNodes = Delete[index, ii];
         
      If [ ri =!= 0,
           
           (* partially reduced *)

           If[ verboseLevel >= 4,
               Print["* Element ", ii , " can be partially reduced"];
           ];
           
           (* Insert remainder on graph *)
           AppendTo[GNodes, m];
           GTree = VertexAdd[GTree, m];
           GTree = EdgeAdd[GTree, Thread[ij -> m]];
           
           (* Insert remainder on basis *)
           Part[r, ii] = ri;
           modified = True;
           
          ,
           
           (* Completely reduced *)

           If[ verboseLevel >= 4,
               Print["* Element ", ii , " can be fully reduced"];
           ];
           
           (* Remove from basis *)
           r = Delete[r, ii];
           ii--; m--;
           If[ m <= 1, Break[]; ];

      ];
    ];
  ];

  Return[ 
    If [ modified
        , 
         DoReduceBasis[r, GTree, GNodes, 
                       symbolicCoefficients, verboseLevel, complete]
        , 
         {r, GTree, GNodes}
    ]
  ];

];

(* Groebner Basis Algortihm *)

NCPolyGroebner[{}, iterations_Integer, opts___Rule] := {{},{}};

NCPolyGroebner[{g__NCPoly}, iterations_Integer, opts___Rule] := Block[
  { i, j, k, kk, l, m, mm, n,
    G, TG,
    OBS = {}, ij, OBSij, 
    q, h, hij,
    reducible, ii, Gii, index, rule,
    symbolicCoefficients,
    sortFirst, simplifyOBS, sortBasis,
    printObstructions, printBasis, printSPolynomials, 
    labels, sortObstructions, reduceBasis, cleanUpBasis,
    removeRedundant,
    verboseLevel, 
    GTree, GNodes },

  (* Process Options *)
  { simplifyOBS, sortBasis,
    printObstructions, printBasis, printSPolynomials,
    labels, sortObstructions, reduceBasis, cleanUpBasis,
    removeRedundant,
    verboseLevel } = 
     { SimplifyObstructions, SortBasis,
       PrintObstructions, PrintBasis, PrintSPolynomials,
       Labels, SortObstructions, ReduceBasis, CleanUpBasis,
       RemoveRedundant,
       VerboseLevel } /. Flatten[{opts}] /. Options[NCPolyGroebner];

  (* Banner *)
  If[ verboseLevel >= 1,
      Print["* * * * * * * * * * * * * * * *"];
      Print["* * *   NCPolyGroebner    * * *"];
      Print["* * * * * * * * * * * * * * * *"];
      If[ verboseLevel >= 2,
          Print["* Options:"];
          Print["> VerboseLevel         -> ", verboseLevel];
          Print["> SortBasis            -> ", sortBasis];
          Print["> SimplifyObstructions -> ", simplifyOBS];
          Print["> SortObstructions     -> ", sortObstructions];
          Print["> PrintObstructions    -> ", printObstructions];
          Print["> PrintBasis           -> ", printBasis];
          Print["> PrintSPolynomials    -> ", printSPolynomials];
      ];
  ];
 
  G = {g};

  (* Set labels *)
  varnum = G[[1,1]];
  labels = If[ labels == {},
    Table[Symbol[FromCharacterCode[ToCharacterCode["@"]+i]], {i, Plus @@ varnum}]
    ,
    Flatten[labels]
  ];
  
  (* Wrap labels *)
  start = Drop[FoldList[Plus, 0, varnum], -1] + 1;
  end = start + varnum - 1;

    (*
     Print["labels = ", labels];
     Print["varnum = ", varnum];
     Print["start = ", start];
     Print["end = ", end];
    *)

  labels = MapThread[Take[labels,{#1,#2}]&, {start, end}];
     (* Print["labels = ", labels]; *)

  (* Symbolic coefficients? *)
  symbolicCoefficients = 
    Not[And @@ Flatten[Map[NumberQ,
                           Map[NCPolyGetCoefficients, G], {2}]]];
    
  If[ symbolicCoefficients && verboseLevel >= 1,
      Print["* Symbolic coefficients detected"];
  ];
    
  If[ verboseLevel >= 1,
    (* Print order *)
    Print["* Monomial order: ", NCPolyDisplayOrder[labels]];
  ];

  If[ verboseLevel >= 3,
    (* Print initial basis *)
    Print["> G(0) = ", ColumnForm[NCPolyDisplay[G, labels]]];
  ];

  (* Simplify and normalize initial relations *)
  If[ verboseLevel >= 1,
      Print["* Reduce and normalize initial set"];
  ];

  m = Length[G];
  G = NCPolyNormalize[NCPolyFullReduce[G]];
  If[ verboseLevel >= 1,
      If[ Length[G] < m, 
          Print[ "> Initial set reduced to '", ToString[Length[G]],
                 "' out of '", ToString[m], "' polynomials" ];
         ,
          Print[ "> Initial set could not be reduced" ];
      ];
  ];

  If[ verboseLevel >= 3,
    (* Print initial basis *)
    Print["> G(0) = ", ColumnForm[NCPolyDisplay[G, labels]]];
  ];

  (* Sort basis *)
  If[ sortBasis, 
      If[ verboseLevel >= 1,
        Print["* Sorting initial basis"];
      ];
      G = Sort[G];
  ];

  If[ printBasis,
      Print["> G(0) = ", ColumnForm[NCPolyDisplay[G, labels]]];
  ];
      
  (* Initialize G tree *)
  m = Length[G];
  If[ verboseLevel >= 2,
      Print["* Initializing G tree"];
  ];
  GNodes = Range[m];
  GTree = Graph[Thread[0 -> GNodes], VertexLabels->"Name"];
      
  If[ verboseLevel >= 3,
      Print["> GTree = ", GTree];
  ];
      
  If[ verboseLevel >= 2,
      Print["* Extracting leading monomials"];
  ];
  TG = Map[NCPolyLeadingMonomial, G];

  If[ verboseLevel >= 3,
      Print["> TG(0) = ", NCPolyDisplay[TG, labels]];
  ];

  (* Compute OBS *)
  If[ verboseLevel >= 1,
      Print["* Computing initial set of obstructions"];
  ];
  mm = m;
  OBSS = {};
  For[ j = 1, j <= m, j++,

       (* Simplify previous obstructions *)
       If[ And[ simplifyOBS, j >= 2 ],
           OBS = NCPolyGroebnerSimplifyObstructions[OBS, TG, j, verboseLevel];
       ];

       (* add new obstructions *)
       OBS = Join[OBS, NCPolyGroebnerObstructions[G, j, simplifyOBS]];
  ];

  If[ printObstructions, 
     Print["* Current obstructions:"];
             Print["> OBS = ", Map[ColumnForm,{OBS[[All,1]], Map[NCPolyDisplay[#, labels]&, Map[Part[#, 2]&, OBS], {3}], OBS[[All,3]]}]];
  ];
 
  (* Iterate *)
  k = 0;
  kk = 0;
  While[ OBS =!= {},

    k++;
    If[ verboseLevel >= 2,
        Print["- Minor Iteration ", k, ", ", Length[G], " polys in the basis, ", Length[OBS], " obstructions"];
    ];

    (* Call Together if symbolic coefficients *)
    If[ symbolicCoefficients,
        G = Map[NCPolyTogether, G];
    ];
         
    If[ printBasis,
        Print["* Current basis:"];
        Print["> G(", ToString[k], ") = ", ColumnForm[NCPolyDisplay[G, labels]]];
        (* Print["> TG(", ToString[k], ") = ", ColumnForm[NCPolyDisplay[TG, labels]]]; *)
    ];

    (* Choose obstruction *)
    sOBS = SelectionFunction[OBS];
    obsdeg = Max[sOBS[[All,3]]];
    (*
    l = If[ sortObstructions
       ,
        If[ verboseLevel >= 3,
          Print["* Sorting obstructions (SUGAR)"];
        ];
        (* Use SUGAR heuristic to sort obstructions *)
        Part[Ordering[Part[OBS, All, 3], 1], 1]
       ,
        (* Pick first one *)
        1
    ];

    (* Print["l = ", l]; *)
    ij = Part[OBS, l, 1];
    OBSij = Part[OBS, l, 2];
    *)
    smaxj = Max[sOBS[[All, 1]][[All, 2]]];
    maxj = Max[OBS[[All, 1]][[All, 2]]];
    (* Print["obsdeg=", obsdeg]; *)
    (* Print["smaxj=", smaxj]; *)
    (* Print["maxj=", maxj]; *)

    If[ smaxj > mm,
      (* Major iteration reached *)
      kk ++;
      mm = maxj;
      If[ verboseLevel >= 1,
        Print["> MAJOR Iteration ", kk, ", ", Length[G], " polys in the basis, ", Length[OBS], " obstructions"];
      ];
      If[ kk >= iterations,
          Break[];
      ];
    ];

    If[ verboseLevel >= 3,
        Print["* Selecting obstructions OBS of degree ", obsdeg];
        If[ printObstructions, 
            Print["* Current obstructions: "];
    Print["> sOBS = ", Map[ColumnForm,{sOBS[[All,1]], Map[NCPolyDisplay[#, labels]&, Map[Part[#, 2]&, sOBS], {3}], sOBS[[All,3]]}]];
        ];
    ];

    (* Remove first term from OBS *)
    (* OBS = Delete[OBS, l]; *)

    (* remove selected obstructions *)
    OBS = Complement[OBS, sOBS];
    If[ verboseLevel >= 3,
        If[ printObstructions,
        Print["> remaining OBS = ", Map[ColumnForm,{OBS[[All,1]], Map[NCPolyDisplay[#, labels]&, Map[Part[#, 2]&, OBS], {3}], OBS[[All,3]]}]];
        ];
    ];

    (* Construct S-Polynomial *)

    (* Get Left and Right parts of the selected obstructions *)
    SParts = Flatten[Map[NCPolySFactorExpand[#[[2]], G[[#[[1,1]]]], G[[#[[1,2]]]]] &, sOBS]];
    If[ verboseLevel >= 3,
        Print["> SParts = ", Map[NCPolyDisplay[#, labels]&, SParts]];
    ];
    newPolys = NCPolyF4Reduction[SParts, G];
    If[ verboseLevel >= 3,
        Print["> newPolys = ", Map[NCPolyDisplay[#, labels]&, newPolys]];
    ];

    (* h = Subtract @@ NCPolySFactorExpand[ OBSij, G[[ij[[1]]]], G[[ij[[2]]]]]; *)
    For[cc=1, cc<=Length[newPolys], cc++,
    h = newPolys[[cc]];
    (* temporary hack so this compiles, since there is no real way of knowing which obs generated this *)
    ij = {1, 1};
    If [ h =!= 0,

         If[ printSPolynomials, 
           Print["* S-Polynomial:"];
           Print["> ", NCPolyDisplay[h, labels]];
         ];

         If[ verboseLevel >= 3,
             Print["* Reducing S-Polynomial"];
         ];

         (* Reduce S-Polynomial *)
         {h,hij} = ReducePolynomial[G,h,labels,
                                    symbolicCoefficients,verboseLevel];

         (* Merge contributions *)
         ij = Union[ij, hij];
         
         ,

         If[ verboseLevel >= 3,
             Print["> Zero S-Polynomial!"];
         ];

    ];

    If [ h =!= 0,

         If[ printSPolynomials, 
             Print["* Reduced S-Polynomial:"];
             Print["> ", NCPolyDisplay[h, labels]];
         ];

         (* Does h divide any poly in the basis? *)
         reducible = Pick[Range[m], 
                          Map[(First[NCPolyReduceWithQuotient[#, 
                                     NCPolyLeadingMonomial[h]]]=!={})&,
                              TG]];
         
         If[ verboseLevel >= 2 && Length[reducible] > 0,
             Print["> ", Length[reducible], 
                   " polys in the current base can be reduced by S-Polynomial"];
         ];
             
         (* Add h to basis *)
         {G,TG,OBS,m,GNodes,GTree} = AddToBasis[G,TG,OBS,
                                                GNodes, GTree,
                                                h,ij,labels,
                                                simplifyOBS,verboseLevel];

         If[ reduceBasis,
             
             If[ verboseLevel >= 2,
                 Print["* Reducing current base"];
             ];
             
             While[ reducible =!= {},
                    
                    ii = First[reducible];
                    reducible = Rest[reducible];
                    
                    If[ verboseLevel >= 3,
                        Print["> Reducing current base poly ", ii];
                    ];

                    (* Reduce candidate *)
                    {Gii,ij} = ReducePolynomial[Delete[G,ii],G[[ii]],labels,
                                                symbolicCoefficients,verboseLevel];

                    (* Remove obstructions involving G[ii] *)
                    OBS = Delete[OBS,
                                 Position[OBS[[All,1]], ii][[All,{1}]]];

                    (* Adjust index in OBS *)
                    index = Insert[Range[m-1], 0, ii];
                    OBS[[All,1,1]] = index[[OBS[[All,1,1]]]];
                    OBS[[All,1,2]] = index[[OBS[[All,1,2]]]];

                    (* Adjust index in reducible *)
                    reducible = index[[reducible]];

                    (* Remove element ii from base *)
                    G = Delete[G, ii];
                    TG = Delete[TG, ii];
                    m -= 1;
                    mm -= 1;

                    (* Make node ii be -1 and adjust other nodes *)
                    rule = Append[
                             Thread[Delete[GNodes, ii] -> Delete[index, ii]],
                             GNodes[[ii]] -> -1
                           ];
                    GTree = VertexReplace[GTree, rule];

                    (* Replace edges containing -1 
                       by edges containing ij *)
                    GTree = EdgeAdd[GTree, 
                      Complement[
                         Flatten[EdgeList[GTree, 
                                          DirectedEdge[-1, 
                                            Except[Alternatives @@ ij]]]
                                   /. Map[List, Thread[-1 -> ij]]]
                        ,
                         EdgeList[GTree, 
                                  DirectedEdge[Alternatives @@ ij, _]]
                      ]
                    ];
                    
                    (* Add node 0 to ij? *)
                    If[ EdgeQ[GTree, 0 -> -1],
                        If[ verboseLevel >= 3,
                            Print["* Node contains 0"];
                        ];
                        AppendTo[ij, 0];
                    ];
                    
                    (* Remove element -1 from GTree *)
                    GTree = VertexDelete[GTree, -1];
                    GNodes = Delete[index, ii];
                    
                    If[ PossibleZeroQ[Gii],
                        
                        (* Completely reduced, remove *)
                        (*
                        If[ MemberQ[ij, 0],
                            (* Mark ij as initial *)
                            GTree = EdgeAdd[GTree, 
                               Complement[
                                  Thread[DirectedEdge[0, DeleteCases[ij, 0]]]
                                 ,
                                  EdgeList[GTree, DirectedEdge[0, _]]
                               ]
                            ];
                        ];
                        *)
                        
                        If[ verboseLevel >= 3,
                            Print["* Removed from GTree"];
                            If[ verboseLevel >= 4,
                                Print["* GTree = ", 
                                         Graph[VertexReplace[GTree, 
                                           Thread[GNodes -> NCPolyDisplay[G]]], 
                                           VertexLabels -> "Name"]];
                                Print["* GNodes = ", GNodes];
                                Print["* Acyclic? = ", AcyclicGraphQ[GTree]];
                            ];
                        ];
                        
                        If[ verboseLevel >= 3,
                            Print["> Poly ", ii, " reduced to zero; removing from base"];
                        ];
                        
                       ,
                        
                        (* Remainder found, add to base *)
                        
                        If[ verboseLevel >= 3,
                            Print["> Poly ", ii, 
                                  " does not reduce to zero;",
                                  " remainder added to base"];
                        ];
                        
                        (* Does Gii divide any poly in the basis? *)
                        mreducible = Pick[Range[m], 
                                          Map[(First[NCPolyReduceWithQuotient[#, 
                                            NCPolyLeadingMonomial[Gii]]]=!={})&,
                                              TG]];
                        
                        (* Add divisible polys to reducible list *)
                        reducible = Union[reducible, mreducible];
                        
                        (* Add Gii back to basis *)
                        {G,TG,OBS,m,GNodes,GTree} = AddToBasis[G,TG,OBS,
                                                               GNodes,GTree,
                                                               Gii,ij,labels,
                                                               simplifyOBS,verboseLevel];

                        If[ verboseLevel >= 3,
                            Print["* Replaced at GTree"];
                            If[ verboseLevel >= 4,
                                Print["* GTree = ", 
                                         Graph[VertexReplace[GTree, 
                                           Thread[GNodes -> NCPolyDisplay[G]]], 
                                           VertexLabels -> "Name"]];
                                Print["* GNodes = ", GNodes];
                                Print["* Acyclic? = ", AcyclicGraphQ[GTree]];
                            ];
                        ];
                    ];
                    
             ];
                  
         ];
         
        ,

         If[ verboseLevel >= 3,
             Print["* S-Polynomial was completely reduced and has been removed from the set of obstructions"];
         ];

    ];
    ];

  ];

  If[ cleanUpBasis,
      (* Cleaning up current basis *)
      If[ verboseLevel >= 1,
          Print["* Cleaning up..."];
      ];
      (* G = NCPolyNormalize[NCPolyFullReduce[G]]; *)
      {G, GTree, GNodes} = DoReduceBasis[G, GTree, GNodes, 
                                         symbolicCoefficients, verboseLevel, True];
  ];

  (* Call Together if symbolic coefficients *)
  If[ symbolicCoefficients,
      G = Map[NCPolyTogether, G];
  ];
      
  (* Remove redundant? *)
  If[ removeRedundant,
      If[ verboseLevel >= 1,
          Print["* Removing redundant polynomials"];
      ];
      {G, GTree} = NCPolyRemoveRedundant[{G, GTree}];
      If[ verboseLevel >= 1,
          Print["* Basis reduced to ",
                ToString[Length[G]], 
                " polynomials"];
          
          If[ verboseLevel >= 4,
              Print["* GTree = ", 
                    Graph[VertexReplace[GTree, 
                                        Thread[DeleteCases[VertexList[GTree],0] -> NCPolyDisplay[G]]], 
                          VertexLabels -> "Name"]];
              Print["* GNodes = ", GNodes];
              Print["* Acyclic? = ", AcyclicGraphQ[GTree]];
          ];
      ];
  ];
      
  If[ OBS =!= {}
     ,
      Message[NCPolyGroebner::Interrupted, Length[G]];
     ,
      If[ verboseLevel >= 1,
          Print["* Found Groebner basis with ", 
                ToString[Length[G]], 
                " polynomials"];
      ];
  ];
      
  If[ verboseLevel >= 1,
      Print["* * * * * * * * * * * * * * * *"];
  ];
  
  Return[{G, GTree}];
];
      
NCPolyRemoveRedundant[{basis_, graph_}, 
                      OptionsPattern[{RedundantDistance -> 1}]] := Block[
  {subgraph, subbasis},

  (*                          
  Print["nodes = ", Thread[DeleteCases[VertexList[GTree],0] -> NCPolyDisplay[G]]]; 
  Print["degrees = ", Thread[VertexList[graph] -> VertexInDegree[graph]]];
  *)
                          
  subgraph = Subgraph[graph, 
                      Pick[VertexList[graph], 
                           VertexInDegree[graph], 
                           _?(# <= OptionValue[RedundantDistance] &)]];
  subbasis = basis[[VertexList[subgraph, Except[0]]]];
                          
  Return[{subbasis, subgraph}];
];

End[];
EndPackage[];
