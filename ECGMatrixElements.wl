(* ::Package:: *)

Import@FileNameJoin[{$snippetDirectory, "physics.wl"}];
Import@FileNameJoin[{$snippetDirectory, "combinatorics.wl"}];
Import@FileNameJoin[{$snippetDirectory, "cppForm.wl"}];

(* Beryllium-9
particleTypes = {1, 1, 1, 1, 2};
charges = {-1, -1, -1, -1, 4};
masses = {1, 1, 1, 1, 16538.028978017737`};
spins = {Up, Down, Up, Down, None};
spaceDim = 3;

Ps-
ECGMatrixElementCodeString[
	{1, 1, 2},
	{-1, -1, 1},
	{1, 1, 1},
	{Up, Down, None},
	3, "psminus_matrix_elements"]

Ps2
ECGMatrixElementCodeString[
	{1, 1, 2, 2},
	{-1, -1, 1, 1},
	{1, 1, 1, 1},
	{Up, Down, Up, Down},
	3, "ps2_matrix_elements"]

Ps2-
ECGMatrixElementCodeString[
	{1, 1, 1, 2, 2},
	{-1, -1, -1, 1, 1},
	{1, 1, 1, 1, 1},
	{Up, Down, Up, Down, Up},
	3, "ps2minus_matrix_elements"]
*)


ECGMatrixElements`Symmetrize1[
		func_, params___, pMats_, signMatrix_][A1_, A2_] := Sum[
	signMatrix[[1, jp]] * func[
		Transpose[pMats[[1]]] . A1 . pMats[[1]],
		Transpose[pMats[[jp]]] . A2 . pMats[[jp]],
		params],
	{jp, Length[pMats]}];

ECGMatrixElements`Symmetrize2[
		func_, params___, pMats_, signMatrix_][A1_, A2_] := Sum[
	signMatrix[[ip, jp]] * func[
		Transpose[pMats[[ip]]] . A1 . pMats[[ip]],
		Transpose[pMats[[jp]]] . A2 . pMats[[jp]],
		params],
	{ip, Length[pMats]}, {jp, Length[pMats]}];

ECGMatrixElements`Overlap[A1_, A2_, spaceDim_Integer] :=
	Det[A1 + A2]^(-spaceDim/2);

ECGMatrixElements`Kinetic[A1_, A2_, spaceDim_Integer, lambda_] :=
	(spaceDim/2) * ECGMatrixElements`Overlap[A1, A2, spaceDim] *
	Tr[lambda . A1 . Inverse[A1 + A2] . A2];

ECGMatrixElements`CoulombPotential[A1_, A2_,
		spaceDim_Integer, charges_List, w_] := With[{
		Ainv = Inverse[A1 + A2],
		dimFactor = Gamma[(spaceDim-1)/2] / Gamma[spaceDim/2]
	},
	ECGMatrixElements`Overlap[A1, A2, spaceDim] * dimFactor * Sum[
		charges[[i]] * charges[[j]] / Sqrt[2 * w[[i,j]] . Ainv . w[[i,j]]],
		{i, Length[charges]}, {j, i+1, Length[charges]}]];


ECGMatrixElements[particleTypes_List, charges_List,
		masses_List, spins_List, spaceDim_Integer] := Module[{
		numParticles, numPairs, allowedPermutations, numPerms,
		spinFactor, signMatrix, lambda, w, pMats, parameterTransformMatrix,
		A1, A2
	},
	numParticles = Length[particleTypes];
	numPairs = numParticles * (numParticles-1) / 2;
	allowedPermutations = stabilizerSubgroup[particleTypes];
	numPerms = Length[allowedPermutations];
	spinFactor = Table[(-1)^(countChanges[spins, perm]/2),
		{perm, allowedPermutations}];
	signMatrix = Table[spinFactor[[ip]] * spinFactor[[jp]] *
		Signature[allowedPermutations[[ip]]] *
		Signature[allowedPermutations[[jp]]],
		{ip, numPerms}, {jp, numPerms}];
	With[{U = jacobiTransformMatrix[masses],
		Uinv = jacobiInverseTransformMatrix[masses]},
		lambda = Most /@ Most[U . DiagonalMatrix[1/masses] . Transpose[U]];
		w = Table[Most[Uinv[[i]] - Uinv[[j]]], {i, numParticles}, {j, numParticles}];
		pMats = Table[Sum[U[[i,k]] * Uinv[[perm[[k]],j]], {k, numParticles}],
			{perm, allowedPermutations}, {i, numParticles-1}, {j, numParticles-1}]];
	parameterTransformMatrix = Table[
		Sum[Subscript[\[FormalK], i, j] * w[[i,j,k]] * w[[i,j,l]],
			{i, numParticles}, {j, i+1, numParticles}],
		{k, numParticles-1}, {l, numParticles-1}];
	A1 = parameterTransformMatrix /. Thread@Rule[
		Flatten@Table[Subscript[\[FormalK], i, j],
			{i, numParticles}, {j, i+1, numParticles}],
		\[FormalX] /@ Range[numPairs]];
	A2 = parameterTransformMatrix /. Thread@Rule[
		Flatten@Table[Subscript[\[FormalK], i, j],
			{i, numParticles}, {j, i+1, numParticles}],
		\[FormalY] /@ Range[numPairs]];
	{ECGMatrixElements`Symmetrize1[
			ECGMatrixElements`Overlap,
			spaceDim, pMats, signMatrix][A1, A2],
		ECGMatrixElements`Symmetrize1[
			ECGMatrixElements`Kinetic,
			spaceDim, lambda, pMats, signMatrix][A1, A2] +
		ECGMatrixElements`Symmetrize1[
			ECGMatrixElements`CoulombPotential,
			spaceDim, charges, w, pMats, signMatrix][A1, A2]}];

ECGMatrixElementCodeString[particleTypes_List, charges_List, masses_List,
		spins_List, spaceDim_Integer, funcName_String] := With[
		{numPairs = Length[particleTypes] * (Length[particleTypes]-1) / 2},
	clangFormat@StringReplace[cppForm[Compile @@
			{Join[\[FormalX] /@ Range[numPairs], \[FormalY] /@ Range[numPairs]],
				ECGMatrixElements[particleTypes, charges, masses, spins, spaceDim],
				CompilationOptions -> {"ExpressionOptimization" -> True}}], {
		"FUNCTION_NAME" -> funcName,
		"cppForm[Instruction[Return]]\n" -> "",
		"cppForm[Instruction[List, {2}, Register[MTensor[Real, 1], 0], {Register[Real, " ~~ \
			ovl___ ~~ "], Register[Real, " ~~ ham___ ~~ "]}]]" :>
			"ovl = R" <> ovl <> ";\nham = R" <> ham <> ";",
		") {" -> ", double &ham, double &ovl) {"}]];
