(* ::Package:: *)

ClearAll[dualNumber,
	deletePairs, dualMultiplicationTable, dualMultiplicationData,
	dualPowerData, dualFunctionDatum, dualFunctionExpr,
	dualFunctionDefinition];

deletePairs = Compile[{{xs, _Integer, 1}},
	Module[{res = Table[0, {0}], len = Length[xs], i = 1},
		While[i <= len,
			If[i == len || xs[[i]] != xs[[i+1]],
				AppendTo[res, xs[[i++]]],
				i+=2]];
		res]];

dualMultiplicationTable[n_Integer] := dualMultiplicationTable[n] = Block[{
	rankSubset = AssociationThread[Subsets@Range[n], Range[2^n]],
	unrankSubset = AssociationThread[Range[2^n], Subsets@Range[n]]},
	Table[Block[{s = Sort@Join[unrankSubset[i], unrankSubset[j]]},
		Lookup[rankSubset, Key[s], 0]],
		{i, 2^n}, {j, 2^n}]];

dualMultiplicationData[n_Integer] := dualMultiplicationData[n] =
	KeyDrop[GroupBy[Tuples[Range[2^n], 2],
		Extract[dualMultiplicationTable[n], #]&], 0];

dualPowerData[n_Integer, 0] := dualPowerData[n, 0] =
	Prepend[Table[<||>, {2^n - 1}], <|{} -> 0|>];

dualPowerData[n_Integer, k_Integer] := dualPowerData[n, k] =
	Table[Module[{assoc = <||>},
		Do[assoc[Sort@Append[indices, First@pair]] = 0,
			{pair, data},
			{indices, Keys@dualPowerData[n, k-1][[Last@pair]]}];
		assoc],
	{data, dualMultiplicationData[n]}];

dualFunctionDatum[n_Integer] := dualFunctionDatum[n] =
	Map[DeleteCases[1]] /@ Keys /@ dualPowerData[n, n];

dualFunctionExpr[n_Integer, f_, x_] :=
	dualNumber @@ Map[Total@*Map[Times[
		Times @@ Map[Indexed[x, #]&, #],
		Derivative[Length@#][f][Indexed[x, 1]]]&],
	dualFunctionDatum[n]];

dualFunctionExpr[n_Integer, k_Integer, f_, x_] :=
	dualNumber @@ Total /@ Map[Total@Map[t \[Function] Times[
			Apply[Times, Indexed[x, {#1, #2}]& @@@ Transpose@{t, #}],
			Apply[(Derivative @@ Lookup[Counts@t, Range@k, 0])[f],
				Indexed[x, {#, 1}]& /@ Range@k]],
		Tuples[Range@k, Length@#]]&,
	dualFunctionDatum@n, {2}];

dualFunctionDefinition[n_Integer, f_] :=
	Module[{vars = Table[Unique[], {2^n}]},
		Inactive[UpSetDelayed][
			f[dualNumber @@ Map[Pattern[#, Blank[]]&, vars]],
			dualFunctionExpr[n, f, vars]]];

dualFunctionDefinition[n_Integer, k_Integer, f_] :=
	Module[{vars = Table[Unique[], {k}, {2^n}]},
		Inactive[UpSetDelayed][
			f @@ dualNumber @@@ Map[Pattern[#, Blank[]]&, vars, {2}],
			dualFunctionExpr[n, k, f, vars]]];


ClearAll[dualFunctionTeX, dualComponentsTeX, dualEquationTeX];

dualFunctionTeX[n_Integer] := dualFunctionTeX[n] =
	StringReplace[Table[riffleJoin[Table[StringJoin[
		ToString@StringForm["x_{``}", #-1]& /@ l,
		ToString@StringForm["f^{(``)}(x_0)", Length@l]],
	{l, ls}], " + "], {ls, dualFunctionDatum[n]}],
	{"f^{(0)}" -> "f", "f^{(1)}" -> "f'",
		"f^{(2)}" -> "f''", "f^{(3)}" -> "f'''"}];

dualComponentsTeX[n_Integer] := dualComponentsTeX[n] =
	If[StringContainsQ[#1, "+"],
		ToString@StringForm["[``]``", #1, #2],
		ToString@StringForm["````", #1, #2]]& @@@ Transpose@{
	dualFunctionTeX[n],
	StringJoin /@ Map[ToString@StringForm["\\varepsilon_{``}", #]&] /@
		Subsets@Range[n]};

dualEquationTeX[n_Integer] := dualEquationTeX[n] =
	"\\begin{aligned}\nf(" <> Inner[StringJoin,
		ToString@StringForm["x_{``}", #-1]& /@ Range[2^n],
		StringJoin /@ Map[ToString@StringForm["\\varepsilon_{``}", #]&] /@
			Subsets@Range[n],
		riffleJoin[" + "]@*List] <>
	") &= " <>
	riffleJoin[dualComponentsTeX[n], " \\\\\n&\\phantom{{}={}} + "] <>
	"\n\\end{aligned}";
