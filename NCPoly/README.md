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

* Get monomial with the largest degree.
* For all g in G check whether m = l g r (probably with NCPolySFactors)
