# Steps to F4

## Root F4 function

* ~~Obstruction selection function.~~

```Mathematica
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
```

* ~~Obstruction complement instead of delete first.~~

```Mathematica
OBS = Complement[OBS, mindegOBS];
```

* ~~Get Left/Right parts of the obstruction.~~

```Mathematica
(* Get Left and Right parts of some obstruction: *)
SParts = NCPolySFactorExpand[ OBSij, G[[ij[[1]]]], G[[ij[[2]]]]];
```

* Reduction ->
* Update basis with each new element.

## -> Reduction

* SymbolicPreprocessing ->
* Row echelon form w.r.t the monomial order.
* Filter elements on whether the leading monomial already appeared.

## -> SymbolicPreprocessing

* ~~Extract all monomials from set of polynomials.~~

```Mathematica
(* polys is a list of NCPoly objects *)
monomials = Flatten[Map[NCPolyToList, polys]]
```

* ~~Get monomial with the largest degree.~~

```Mathematica
(* Get maximal degree *)
maxdeg = Max[Map[NCPolyDegree, monomials]];
(* Select the first monomial with maximal degree *)
Select[monomials, NCPolyDegree[#] == maxdeg &][[1]]
```

* For all g in G check whether m = l g r (probably with NCPolySFactors)

```Mathematica
Clear[GetDivisors];
GetDivisors[G_List, m_NCPoly] := Module[
    {i, OBSi = {}, OBS = {}, d, DIV = {}},
    For[i = 1, i <= Length[G], i++,
        OBSi = NCPolySFactors[G[[i]], m];
        d = NCPolyDegree[m];
        If[OBSi =!= {},
            d += Apply[Plus, Map[NCPolyDegree, OBSi[[All, 2]], {2}], {1}];
            OBS = MapThread[{{i, Length[G] + 1}, #1, #2} &, {OBSi, d}];
            OBS = OBS[[All, 2]];
            OBS = Map[NCPolySFactorExpand[#, G[[i]], m] &, OBS];
            DIV = Join[DIV, OBS[[All, 1]]];
        ];
    ];
    Return[DIV];
];
```
