(* ::Package:: *)

cartesianVariables[d_Integer] := Table[Indexed[\[FormalX], i],
	{i, d}];

hyperangularVariables[d_Integer] := Append[
	Table[Indexed[\[FormalTheta], i], {i, d-1}], \[FormalPhi]];

hypersphericalVariables[d_Integer] := Prepend[
	hyperangularVariables[d-1], \[FormalR]];


fromHyperangularCoordinates[d_Integer] := Join[
	{Cos[\[FormalPhi]], Sin[\[FormalPhi]]} * Product[
		Sin[Indexed[\[FormalTheta], i]],
		{i, d-1}],
	Table[Cos[Indexed[\[FormalTheta], k]] * Product[
		Sin[Indexed[\[FormalTheta], i]],
		{i, k+1, d-1}],
	{k, d-1}]];

hyperangularAssumptions[d_Integer] := And @@ Join[
	Table[0 < Indexed[\[FormalTheta], i] < \[Pi], {i, d-1}],
	{-\[Pi] < \[FormalPhi] < \[Pi]}];

hyperangularRanges[d_Integer] := Join[
	Table[{Indexed[\[FormalTheta], i], 0, \[Pi]}, {i, d-1}],
	{{\[FormalPhi], -\[Pi], \[Pi]}}];

hyperangularLaplacian[d_Integer] := Module[
	{f = \[FormalF] @@ hyperangularVariables[d]},
	Product[Csc[Indexed[\[FormalTheta], i]]^2, {i, d-1}] * D[f, {\[FormalPhi], 2}] +
	Sum[Product[Csc[Indexed[\[FormalTheta], j]]^2, {j, i+1, d-1}] *
		D[f, {Indexed[\[FormalTheta], i], 2}],
		{i, d-1}] +
	Sum[i * Cot[Indexed[\[FormalTheta], i]] *
		Product[Csc[Indexed[\[FormalTheta], j]]^2, {j, i+1, d-1}] *
		D[f, Indexed[\[FormalTheta], i]],
		{i, d-1}]];


fromHypersphericalCoordinates[d_Integer] :=
	\[FormalR] * fromHyperangularCoordinates[d-1];

toHypersphericalCoordinates[d_Integer] := Join[
	{Sqrt@Sum[Indexed[\[FormalX], i]^2, {i, d}]},
	Table[ArcTan[Indexed[\[FormalX], k],
		Sqrt@Sum[Indexed[\[FormalX], i]^2, {i, k-1}]],
		{k, 3, d}],
	{ArcTan[Indexed[\[FormalX], 1], Indexed[\[FormalX], 2]]}];

hypersphericalAssumptions[d_Integer] :=
	hyperangularAssumptions[d-1] && \[FormalR] > 0;

hypersphericalRanges[d_Integer] := Prepend[
	hyperangularRanges[d-1], {\[FormalR], 0, \[Infinity]}];

hypersphericalLaplacian[d_Integer] := Module[
	{f = \[FormalF] @@ hypersphericalVariables[d]},
	D[f, {\[FormalR], 2}] +
	(d-1)/\[FormalR] * D[f, \[FormalR]] +
	1/\[FormalR]^2 * Product[Csc[Indexed[\[FormalTheta], i]]^2, {i, d-2}] * D[f, {\[FormalPhi], 2}] +
	Sum[1/\[FormalR]^2 * Product[Csc[Indexed[\[FormalTheta], j]]^2, {j, i+1, d-2}] *
			D[f, {Indexed[\[FormalTheta], i], 2}],
		{i, d-2}] +
	Sum[i/\[FormalR]^2 * Cot[Indexed[\[FormalTheta], i]] *
			Product[Csc[Indexed[\[FormalTheta], j]]^2, {j, i+1, d-2}] *
			D[f, Indexed[\[FormalTheta], i]],
		{i, d-2}]];


(*
Self-consistency checking code.
Should output all zeroes when run.

Table[Subtract[hyperangularLaplacian[d],
	hypersphericalLaplacian[d+1] /. \[FormalR] \[Rule] 1 //. {
		Derivative[0, j__][\[FormalF]][1, vars__] \[RuleDelayed] Derivative[j][\[FormalF]][vars],
		Derivative[1|2, j__][\[FormalF]][1, vars__] \[RuleDelayed] 0}],
	{d, 1, 10}]

Table[Assuming[hypersphericalAssumptions[d],
	FullSimplify[hypersphericalLaplacian[d] - Laplacian[
		\[FormalF] @@ toHypersphericalCoordinates[d],
		cartesianVariables[d]
	] /. Thread[cartesianVariables[d] \[Rule]
		fromHypersphericalCoordinates[d]]]],
	{d, 2, 4}]

Table[Subtract[cartesianVariables[d],
	fromHypersphericalCoordinates[d] /. Thread[
	hypersphericalVariables[d] \[Rule]
		toHypersphericalCoordinates[d]]],
	{d, 2, 10}]

Table[Subtract[hypersphericalVariables[d],
	Assuming[hypersphericalAssumptions[d],
		FullSimplify[toHypersphericalCoordinates[d] /.
		Thread[cartesianVariables[d] \[Rule]
			fromHypersphericalCoordinates[d]]]]],
	{d, 2, 10}]

*)
