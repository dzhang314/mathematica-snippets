(* ::Package:: *)

Import[FileNameJoin[{NotebookDirectory[],
	"combinatorics.wl"}]];
Import[FileNameJoin[{NotebookDirectory[],
	"hypersphericalCoordinates.wl"}]];

ClearAll[monomials, harmonicPolynomialBasis];

monomials[numVars_Integer, degree_Integer] :=
	Times @@ Power[Indexed[\[FormalX], #]& /@ Range[numVars], #]& /@
		Reverse /@ orderedIntegerPartitions[numVars, 0][degree];
(* Note: Length[monomials[i, j]] \[Equal] Binomial[i+j-1, j] *)

harmonicPolynomialBasis[numVars_Integer, 0] := monomials[numVars, 0];
harmonicPolynomialBasis[numVars_Integer, 1] := monomials[numVars, 1];

harmonicPolynomialBasis[numVars_Integer, 2] :=
	Dot[Reverse@NullSpace@List@
		Laplacian[monomials[numVars, 2],
			Indexed[\[FormalX], #]& /@ Range[numVars]],
		monomials[numVars, 2]];

harmonicPolynomialBasis[numVars_Integer, degree_Integer] :=
	Dot[Reverse@NullSpace@Transpose@Outer[Coefficient,
			Laplacian[monomials[numVars, degree],
				Indexed[\[FormalX], #]& /@ Range[numVars]],
			monomials[numVars, degree-2]],
		monomials[numVars,degree]];

ClearAll[sphericalInnerProduct, sphericalHarmonicBasis];

sphericalInnerProduct[sphereDim_Integer, degree_Integer] :=
	sphericalInnerProduct[sphereDim, degree] =
		Module[{monoms, prods},
			monoms = monomials[sphereDim + 1, degree];
			prods = Outer[Times, monoms, monoms];
			Integrate[prods, \[FormalX] \[Element] Sphere[sphereDim + 1]] /
				RegionMeasure[Sphere[sphereDim + 1]]];

sphericalHarmonicBasis[sphereDim_Integer, degree_Integer] :=
	sphericalHarmonicBasis[sphereDim, degree] =
		Dot[Orthogonalize[
			Outer[Coefficient,
				harmonicPolynomialBasis[sphereDim+1, degree],
				monomials[sphereDim+1, degree]],
			#1.sphericalInnerProduct[sphereDim, degree].#2 &],
		monomials[sphereDim+1, degree]];

hyperangularAreaElement[d_Integer] :=
	Product[Sin[Indexed[\[FormalTheta], i]]^i, {i, d-1}];

hypersphericalAreaElement[d_Integer] :=
	\[FormalR]^(d-1) * hyperangularAreaElement[d-1];


Select[FileNames[], StringMatchQ@StringExpression[
	"sphericalInnerProduct_",
	DigitCharacter..,
	"_",
	DigitCharacter..,
	".m"]]


sphericalInnerProduct[2, 9]


sphereDim = 3;
degree = 3;

sphHarms = sphericalHarmonicBasis[sphereDim, degree] /. Thread[
	cartesianVariables[sphereDim+1] -> fromHyperangularCoordinates[sphereDim]];

areaElement = hyperangularAreaElement[sphereDim];

Map[Integrate @@ Prepend[hyperangularRanges[sphereDim], #]&,
	areaElement*Outer[Times, sphHarms, sphHarms], {2}] /
	RegionMeasure[Sphere[sphereDim + 1]]
