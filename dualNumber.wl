(* ::Package:: *)

ClearAll[$f, $x, $y, $a, termList, dropTail,
	dualUnit, dualNumber, dualProduct, dualInverse, dualPower, dualFunction,
	dualFunctionData, dualFunctionFromData];

termList[0] = {};
termList[expr_] := With[{expanded = Expand@expr},
	If[Head@expanded === Plus, List @@ expanded, {expanded}]];

dropTail[elem_][xs_List] := If[Last@xs === elem, dropTail[elem][Most@xs], xs];

Times[dualUnit[i_], dualUnit[i_]] ^:= 0;
Power[dualUnit[i_], n_] /; n > 1 ^:= 0;

dualNumber[x_, n_] := Dot[(Indexed[x, #]& /@ Range[2^n]),
	Times @@@ Map[dualUnit] /@ Subsets@Range@n];

dualProduct[n_Integer] := dualProduct[n] = Module[
	{expr = Expand[dualNumber[$x, n] dualNumber[$y, n]]},
	Reverse@First@Last@Reap@Do[
		With[{dualFactor = Times @@ dualUnit /@ subset},
			If[dualFactor === 1, Sow@expr,
				Sow@Coefficient[expr, dualFactor];
				expr -= Coefficient[expr, dualFactor] * dualFactor;
				expr = Expand@expr]],
		{subset, Reverse@Subsets@Range@n}]];
dualProduct[n_Integer, x_, y_] := dualProduct[n] /. {$x -> x, $y -> y};

dualInverse[n_Integer] := dualInverse[n] = ReplaceAll[
	Indexed[$y, #]& /@ Range[2^n], First@Solve[
		LogicalExpand[dualProduct[n] == UnitVector[2^n, 1]],
		Indexed[$y, #]& /@ Range[2^n]]];

dualPower[n_Integer, 0] := UnitVector[2^n, 1];
dualPower[n_Integer, 1] := Indexed[$x, #] & /@ Range[2^n];
dualPower[n_Integer, 2] := dualPower[n, 2] = dualProduct[n] /. $y -> $x;
dualPower[n_Integer, k_Integer] := dualPower[n, k] = Expand[
	dualProduct[n] /. $y -> dualPower[n, k - 1]];

dualFunction[n_Integer] := dualFunction[n] = Table[
	Expand@Sum[With[{k = FirstCase[term, $a[k_] :> k, 0]},
		Derivative[k][$f][Indexed[$x, 1]] * (
			Times @@ FactorList[term / (k! $a[k])][[2 ;;, 1]])],
		{term, termList@First@CoefficientList[expr, Indexed[$x, 1]]}],
	{expr, Expand@Sum[$a[k] dualPower[n, k], {k, 0, n}]}];
dualFunction[n_Integer, f_, x_] := dualFunction[n] /. {$f -> f, $x -> x};

dualFunctionData[n_Integer] := dualFunctionData[n] = dropTail[{}] /@ Table[
	FactorList[term][[2 ;;, 1, 2, 1]],
	{expr, Rest@dualFunction[n]}, {k, n},
	{term, termList@Coefficient[expr, Derivative[k][$f][Indexed[$x, 1]]]}];

dualFunctionFromData[data_] := Table[Expand@Dot[
		Derivative[#][$f][Indexed[$x, 1]] & /@ Range@Length@list,
		Total /@ Apply[Times, Map[Indexed[$x, #] &, list, {3}], {2}]],
	{list, data}] ~Prepend~ $f[Indexed[$x, 1]];

dualMultivariateFunction[dualOrder_Integer, numVars_Integer] :=
	Prepend[
		Table[
			Sum[Times[
				Product[Indexed[$x[tup[[i]]], par[[i]]], {i, k}],
				Apply[(Derivative @@ Lookup[Counts[tup], Range[numVars], 0])[$f],
					Table[Indexed[$x[i], 1], {i, numVars}]]],
			{k, Length[dat]},
			{par, dat[[k]]},
			{tup, Tuples[Range[numVars], k]}],
		{dat, dualFunctionData[dualOrder]}],
	$f @@ Table[Indexed[$x[i], 1], {i, numVars}]];
