(* ::Package:: *)

Import@FileNameJoin[{$snippetDirectory, "combinatorics.wl"}];
Import@FileNameJoin[{$snippetDirectory, "hypersphericalCoordinates.wl"}];


ClearAll[monomials, harmonicPolynomialBasis];

(* Note: Length[monomials[i, j]] \[Equal] Binomial[i + j - 1, j] *)
monomials[numVars_Integer, degree_Integer] :=
	Times @@ Power[Indexed[\[FormalX], #]& /@ Range[numVars], #]& /@
		Reverse /@ orderedIntegerPartitions[numVars, 0][degree];

(* 1 is the unique polynomial of degree 0, and it is harmonic. *)
harmonicPolynomialBasis[numVars_Integer, 0] = {1};
(* All polynomials of degree 1 are harmonic. *)
harmonicPolynomialBasis[numVars_Integer, 1] := cartesianVariables[numVars];
(* There are no nonzero polynomials of degree \[GreaterEqual] 2 in 0 variables. *)
harmonicPolynomialBasis[0, degree_Integer] = {};
(* For degree \[GreaterEqual] 2, no polynomials in 1 variable are harmonic. *)
harmonicPolynomialBasis[1, degree_Integer] = {};

harmonicPolynomialBasis[numVars_Integer, 2] :=
	Dot[Reverse@NullSpace@List@Laplacian[
			monomials[numVars, 2],
			Indexed[\[FormalX], #]& /@ Range[numVars]],
		monomials[numVars, 2]];

harmonicPolynomialBasis[numVars_Integer, degree_Integer] :=
	Dot[Reverse@NullSpace@Transpose@Outer[Coefficient,
			Laplacian[monomials[numVars, degree],
				Indexed[\[FormalX], #]& /@ Range[numVars]],
			monomials[numVars, degree-2]],
		monomials[numVars,degree]];


ClearAll[sphericalInnerProduct, sphericalHarmonicBasis];

(*
Hold[sphericalInnerProduct[ToExpression[#1], ToExpression[#2]] =
	Import["sphericalInnerProduct_" <> #1 <> "_" <> #2 <> ".m"]] & @@@
		Join @@ StringCases[FileNames[], StringExpression[
			"sphericalInnerProduct_",
			dim : DigitCharacter..,
			"_",
			deg : DigitCharacter..,
			".m"
		] :> {dim, deg}
] // Map[ReleaseHold];
*)

(* 1 is the only monomial of degree 0, and its integral is 1. *)
sphericalInnerProduct[sphereDim_Integer, 0] = SparseArray[{{1}}];
(* The only polynomial of degree k in 1 variable is x^k. *)
(* Its square x^2k is constant when restricted to the 0-sphere. *)
sphericalInnerProduct[0, degree_Integer] = SparseArray[{{1}}];

sphericalInnerProduct[sphereDim_Integer, degree_Integer] :=
sphericalInnerProduct[sphereDim, degree] =
	Module[{monoms, prods, ans},
		monoms = monomials[sphereDim + 1, degree];
		prods = Outer[Times, monoms, monoms];
		ans = Integrate[prods, \[FormalX] \[Element] Sphere[sphereDim + 1]] /
			RegionMeasure[Sphere[sphereDim + 1]];
		ans = SparseArray[ans];
		Export[StringJoin[
				"sphericalInnerProduct_",
				ToString[sphereDim],
				"_",
				ToString[degree],
				".m"],
			ans];
		ans];

(* 1 is the only polynomial of degree 0, and it is normalized. *)
sphericalHarmonicBasis[sphereDim_Integer, 0] = {1};
(* The coordinate functions are the polynomials of degree 1. *)
(* They are harmonic, and normalized by Sqrt[dim+1]. *)
sphericalHarmonicBasis[sphereDim_Integer, 1] :=
	Sqrt[sphereDim+1] * cartesianVariables[sphereDim+1];
(* There are no harmonic polynomials of degree \[GreaterEqual] 2 in 1 variable. *)
sphericalHarmonicBasis[0, degree_Integer] = {};

sphericalHarmonicBasis[sphereDim_Integer, degree_Integer] :=
sphericalHarmonicBasis[sphereDim, degree] =
	Dot[Orthogonalize[
		Outer[Coefficient,
			harmonicPolynomialBasis[sphereDim+1, degree],
			monomials[sphereDim+1, degree]],
		#1.sphericalInnerProduct[sphereDim, degree].#2 &],
	monomials[sphereDim+1, degree]];

(* Note: Length[sphericalHarmonicBasis[dim, deg]] \[Equal]
	Binomial[dim + deg, deg] - Binomial[dim + deg - 2, deg - 2] *)


(*
Self-consistency check. Should output an identity matrix.

sphereDim = 2;
degree = 3;

sphHarms = sphericalHarmonicBasis[sphereDim, degree] /. Thread[
	cartesianVariables[sphereDim+1] \[Rule]
		fromHyperangularCoordinates[sphereDim]];

Map[Integrate @@ Prepend[hyperangularRanges[sphereDim], #]&,
	hyperangularAreaElement[sphereDim] *
		Outer[Times, sphHarms, sphHarms], {2}] /
	RegionMeasure[Sphere[sphereDim + 1]]
*)


ClearAll[angularMomentum, totalAngularMomentum,
	sphericalHarmonicQuantumNumbers];

angularMomentum[f_, i_Integer, j_Integer] :=
	Indexed[\[FormalX], i] D[f, Indexed[\[FormalX], j]] -
	Indexed[\[FormalX], j] D[f, Indexed[\[FormalX], i]];

totalAngularMomentum[f_, d_Integer] := Module[{i, j},
	Sum[-angularMomentum[angularMomentum[f, i, j], i, j],
		{i, d}, {j, i+1, d}]];

sphericalHarmonicQuantumNumbers[sphereDim_Integer, degree_Integer] :=
sphericalHarmonicQuantumNumbers[sphereDim, degree] =
	Table[FullSimplify[totalAngularMomentum[f, d] / f],
		{f, sphericalHarmonicBasis[sphereDim, degree]},
		{d, 2, sphereDim+1}];


ClearAll[generalHomogeneousPolynomial,
	generalHomogeneousLaplacian,
	generalHarmonicDecomposition,
	generalHarmonicPart];

generalHomogeneousPolynomial[numVars_Integer, degree_Integer] :=
	Dot[monomials[numVars, degree], Indexed[\[FormalA], #] & /@
		Range@Binomial[numVars + degree - 1, degree]];

generalHomogeneousLaplacian[0, n_Integer, k_Integer] :=
	If[n == k == 0, Indexed[\[FormalA], 1], 0];
generalHomogeneousLaplacian[d_Integer, n_Integer, 0] :=
	generalHomogeneousPolynomial[d, n];
generalHomogeneousLaplacian[d_Integer, n_Integer, k_Integer] :=
generalHomogeneousLaplacian[d, n, k] =
	Laplacian[generalHomogeneousLaplacian[d, n, k - 1],
		cartesianVariables[d]];

generalHarmonicDecomposition[d_Integer, n_Integer] :=
generalHarmonicDecomposition[d, n] = Table[
	Sum[Divide[
		(-Total[cartesianVariables[d]^2])^j *
			generalHomogeneousLaplacian[d, n, j+(n-m)/2],
		(n-m)!! * (2j)!! * FactorialPower[d+2m-4, j, 2] *
			FactorialPower[d+n+m-2, (n-m)/2, 2]],
		{j, 0, Floor[m/2]}],
	{m, n, 0, -2}];

generalHarmonicPart[d_Integer, n_Integer] :=
generalHarmonicPart[d, n] = Sum[Divide[
	(-Total[cartesianVariables[d]^2])^j *
		generalHomogeneousLaplacian[d, n, j],
	(2j)!! * FactorialPower[d+2n-4, j, 2]],
	{j, 0, Floor[n/2]}];


(*
Self-consistency check. Should output all zeroes.

Table[Expand@Laplacian[
		generalHarmonicDecomposition[d, n],
		cartesianVariables[d]],
	{d, 4}, {n, 0, 6}]

Table[Expand[generalHomogeneousPolynomial[d, n] - Dot[
		Total[cartesianVariables[d]^2]^Range[0, Floor[n/2]],
		generalHarmonicDecomposition[d, n]]],
	{d, 4}, {n, 0, 6}]
*)


ClearAll[normalizedSphericalHarmonics,
	normalizeSphericalHarmonic, normSphHarm, sphHarmCoeffs];

normalizedSphericalHarmonics[dim_, deg_] := Expand@Divide[
	sphericalHarmonicBasis[dim, deg],
	Sqrt@FactorialPower[dim + 2*deg - 1, deg, 2]];

normalizeSphericalHarmonic[sphHarm_] := Module[{dim, deg, f1, f2},
	dim = Max[0, Cases[sphHarm, Indexed[\[FormalX], {i_}] :> i, All]];
	If[dim == 0, Return[1]];
	deg = assertFirst@Union[Total /@ Outer[Exponent,
		MonomialList[sphHarm],
		cartesianVariables[dim]]];
	f1 = Sqrt@Dot[sphericalIntegralTable[dim - 1, 2*deg],
		Coefficient[sphHarm^2, monomials[dim, 2*deg]]];
	f2 = Sqrt@FactorialPower[dim + 2*deg - 2, deg, 2];
	sphHarm / f1 / f2];

normSphHarm[sphHarm_] := Module[{dim, deg, f1, f2},
	dim = Max[0, Cases[sphHarm, Indexed[\[FormalX], {i_}] :> i, All]];
	If[dim == 0, Return[1]];
	deg = assertFirst@Union[Total /@ Outer[Exponent,
		MonomialList[sphHarm],
		cartesianVariables[dim]]];
	f1 = Sqrt[Integrate[sphHarm^2, \[FormalX] \[Element] Sphere[dim]] /
		RegionMeasure@Sphere[dim]];
	f2 = Sqrt@FactorialPower[dim + 2*deg - 2, deg, 2];
	sphHarm / f1 / f2];

sphHarmCoeffs[sphHarm_] := Module[{dim, deg, f1, f2},
	dim = Max[0, Cases[sphHarm, Indexed[\[FormalX], {i_}] :> i, All]];
	If[dim == 0, Return[1]];
	deg = assertFirst@Union[Total /@ Outer[Exponent,
		MonomialList[sphHarm],
		cartesianVariables[dim]]];
	Coefficient[sphHarm, monomials[dim, deg]]];


ClearAll[sphericalHarmonicW];

sphericalHarmonicW[0 ...] = 1;

sphericalHarmonicW[1] = Indexed[\[FormalX], 1];

sphericalHarmonicW[deg_, j_, k___] :=
sphericalHarmonicW[deg, j, k] = Module[{dim, r, r2},
	dim = Length[{k}] + 2;
	r = Indexed[\[FormalX], #]& /@ Range[dim];
	r2 = r.r;
	Expand@Dot[Table[(-r2)^i /
			((2i)!! * FactorialPower[dim + 2*deg - 4, i, 2]),
			{i, 0, Floor[deg/2]}],
		NestList[Laplacian[#, r] &,
			sphericalHarmonicW[j, k] * Indexed[\[FormalX], dim]^(deg - j),
			Floor[deg/2]]]];

ClearAll[sphericalHarmonicRange];

sphericalHarmonicRange[0, deg_Integer] :=
	If[0 <= deg <= 1, {{deg}}, {}];

sphericalHarmonicRange[dim_Integer, deg_Integer] :=
sphericalHarmonicRange[dim, deg] =
	Prepend[deg] /@ Join @@ Table[
		sphericalHarmonicRange[dim - 1, k],
		{k, deg, 0, -1}];


(*
Self-consistency check. Should output all zeroes with no errors.

Table[Expand[normalizedSphericalHarmonics[dim, deg]-
	normSphHarm /@ sphericalHarmonicW @@@
		sphericalHarmonicRange[dim, deg]],
	{dim, 0, 4}, {deg, 0, 4}]
*)


ClearAll[hypersphericalHarmonicY];

hypersphericalHarmonicY[m_Integer] :=
hypersphericalHarmonicY[m] =
	(Indexed[\[FormalX], 1] + Sign[m] I Indexed[\[FormalX], 2])^Abs[m];

hypersphericalHarmonicY[k_Integer, m_Integer] :=
hypersphericalHarmonicY[k, m] = Module[{r},
	r = Sqrt@Total[cartesianVariables[3]^2];
	FullSimplify[r^(k - Abs[m]) *
		GegenbauerC[k - Abs[m], 1/2 + Abs[m], Indexed[\[FormalX], 3]/r] *
		hypersphericalHarmonicY[m]]];

hypersphericalHarmonicY[j_Integer, k_Integer, m : _Integer..] :=
hypersphericalHarmonicY[j, k, m] = Module[{d, r},
	d = Length@{m} + 3;
	r = Sqrt@Total[cartesianVariables[d]^2];
	FullSimplify[r^(j - k) *
		GegenbauerC[j - k, d/2 - 1 + k, Indexed[\[FormalX], d]/r] *
		hypersphericalHarmonicY[k, m]]];


ClearAll[trigIntegratePi, trigIntegrate2Pi, sphInnProd];

trigIntegratePi[m_Integer, n_Integer] :=
trigIntegratePi[m, n] =
	If[OddQ[n], 0, Beta[(m+1)/2, (n+1)/2]];

trigIntegrate2Pi[m_Integer, n_Integer] :=
trigIntegrate2Pi[m, n] =
	If[OddQ[m] || OddQ[n], 0, 2*Beta[(m+1)/2, (n+1)/2]];

sphInnProd[0, deg_Integer] := SparseArray[{{1}}];

sphInnProd[dim_Integer, deg_Integer] := Module[{
		parts = ToPackedArray[Reverse /@
			orderedIntegerPartitions[dim + 1, 0][deg]],
		tc = ToPackedArray@Join[{
				Append[ConstantArray[{1, 0}, dim - 1], {0, 1}],
				ConstantArray[{1, 0}, dim]},
			Table[Join[
				ConstantArray[{0, 0}, k - 1],
				{{0, 1}},
				ConstantArray[{1, 0}, dim - k - 1],
				{{0, 0}}],
			{k, dim - 1}]],
		ta = ToPackedArray@Append[
			Table[{k, 0}, {k, dim - 1}], {0, 0}],
		arr = {}, tup, ans},
	Do[
		tup = (parts[[i]] + parts[[j]]).tc + ta;
		ans = Times[trigIntegrate2Pi @@ Last[tup],
			Times @@ trigIntegratePi @@@ Most[tup],
			RegionMeasure@Sphere[dim + 1]^-1];
		If[ans != 0, AppendTo[arr, {i, j} -> ans]],
	{i, Length[parts]}, {j, Length[parts]}];
	SparseArray[arr]];


ClearAll[sphericalIntegralTable];
sphericalIntegralTable[0, deg_Integer] := {1 - Mod[deg, 2]};

sphericalIntegralTable[dim_Integer, deg_Integer] :=
sphericalIntegralTable[dim, deg] = Module[{
		tc = ToPackedArray@Join[{
				Append[ConstantArray[{1, 0}, dim - 1], {0, 1}],
				ConstantArray[{1, 0}, dim]},
			Table[Join[
				ConstantArray[{0, 0}, k - 1],
				{{0, 1}},
				ConstantArray[{1, 0}, dim - k - 1],
				{{0, 0}}],
			{k, dim - 1}]],
		ta = ToPackedArray@Append[
			Table[{k, 0}, {k, dim - 1}], {0, 0}]},
	mapMonitored[With[{tup = Reverse[#].tc + ta},
		Times[trigIntegrate2Pi @@ Last[tup],
			Times @@ trigIntegratePi @@@ Most[tup],
			RegionMeasure@Sphere[dim + 1]^-1]] &,
		orderedIntegerPartitions[dim + 1, 0][deg]]];
