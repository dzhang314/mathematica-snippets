(* ::Package:: *)

ClearAll[Wedge, Vee, Square];
SetAttributes[Wedge, {Orderless, Flat, OneIdentity}];
SetAttributes[Vee, {Orderless, Flat, OneIdentity}];

ClearAll[exactlyOneCNF, sudokuExpr,
	sudokuBoolExpr, reducedSudokuBoolExpr`Temp,
	sudokuReductionRules, reducedSudokuBoolExpr,
	sudokuVars, reducedSudokuVarList, reducedSudokuVars,
	sudokuGraph, toSudokuGrid, reducedSudokuGrids];

exactlyOneCNF[vars_List] := Wedge[Vee @@ vars,
	Wedge @@ Vee @@@ Map[Square] /@ Subsets[vars, {2}]];

sudokuExpr[s_Integer] := sudokuExpr[s] = Wedge[
	Wedge @@ Flatten@Table[exactlyOneCNF@Table[f[i, j, n],
		{i, s^2}], {j, s^2}, {n, s^2}],
	Wedge @@ Flatten@Table[exactlyOneCNF@Table[f[i, j, n],
		{j, s^2}], {n, s^2}, {i, s^2}],
	Wedge @@ Flatten@Table[exactlyOneCNF@Table[f[i, j, n],
		{n, s^2}], {i, s^2}, {j, s^2}],
	Wedge @@ Flatten@Table[exactlyOneCNF@Flatten@Table[f[i, j, n],
		{i, (a-1)s+1, a s}, {j, (b-1)s+1, b s}],
		{a, s}, {b, s}, {n, s^2}]
	] //. {
		Wedge[xs___] :> Wedge @@ Union[{xs}],
		Vee[xs___] :> Vee @@ Union[{xs}]
	};

sudokuBoolExpr[s_Integer] := sudokuBoolExpr[s] = sudokuExpr[s] /.
	{Square -> Not, Vee -> Or, Wedge -> And};

reducedSudokuBoolExpr`Temp[s_Integer] := reducedSudokuBoolExpr`Temp[s] =
	sudokuBoolExpr[s] /. f[1, j_, n_] :> j === n;

sudokuReductionRules[s_Integer] := sudokuReductionRules[s] =
	Thread@Rule[List @@ Select[
		reducedSudokuBoolExpr`Temp[s], EqualTo[1]@*Length
	][[All, 1]], False];

reducedSudokuBoolExpr[s_Integer] := reducedSudokuBoolExpr[s] =
	reducedSudokuBoolExpr`Temp[s] /. sudokuReductionRules[s];

sudokuVars[s_Integer] := sudokuVars[s] = Flatten @ Outer[
	f, Range[s^2], Range[s^2], Range[s^2]];

reducedSudokuVarList[s_Integer] := reducedSudokuVarList[s] =
	sudokuVars[s] /. f[1, j_, n_] :> j === n /. sudokuReductionRules[s];

reducedSudokuVars[s_Integer] := reducedSudokuVars[s] =
	DeleteCases[reducedSudokuVarList[s], True | False];

sudokuGraph[s_Integer] := sudokuGraph[s] = Graph[sudokuVars[s],
	List @@ Select[sudokuExpr[s], EqualTo[2] @* Length] /. {
		Square -> Identity, Vee-> UndirectedEdge}];

toSudokuGrid[s_Integer] := With[{ps2 = Partition[#, s^2]&},
	ps2 @* Map[Last] @* Position[True] @* ps2 @* ps2];

reducedSudokuGrids[1] = {{{1}}};
reducedSudokuGrids[2] = toSudokuGrid[2][reducedSudokuVarList[2] /.
	Thread[reducedSudokuVars[2] -> #]]& /@ SatisfiabilityInstances[
		reducedSudokuBoolExpr[2], reducedSudokuVars[2], All];


su3 = SatisfiabilityInstances[reducedSudokuBoolExpr[3], reducedSudokuVars[3]];


While[True,
	distinctExpr = And @@ Table[Or @@ MapThread[
		If[#1, !#2, #2]&, {g, reducedSudokuVars[3]}], {g, su3}];
	su3 = Join[su3, SatisfiabilityInstances[
		reducedSudokuBoolExpr[3] && distinctExpr, reducedSudokuVars[3]]]];


gridVars = reducedSudokuVarList[3] /. Thread[reducedSudokuVars[3] -> su3[[1]]];
gridExpr = Or @@ MapThread[If[#1, !#2, #2]&, {gridVars, sudokuVars[3]}];
grid = toSudokuGrid[3][gridVars];


grids = {};
s = 3;

expand[grid_] := ReplacePart[grid, #]& /@
	Thread[Position[grid, _Integer] -> Null];

uniqueSolutionQ[grid_] := uniqueSolutionQ[grid] =
	!SatisfiableQ[sudokuBoolExpr[s] && gridExpr && Apply[And,
		f[##, grid[[##]]]& @@@ Position[grid, _Integer]]];

search[grid_] := Module[
	{exp = expand[grid], prog = 0, irred = True},
	Monitor[
		Do[++prog;
			If[uniqueSolutionQ[g],
				irred = False;
				search[g]],
			{g, exp}];
		If[irred, AppendTo[grids, grid]],
		ProgressIndicator[prog / Length[exp]]];
	search[grid] = Null];


search[grid]
