(* ::Package:: *)

hydrogenRadialWavefunction[n_, l_][r_] := Module[
	{normFac = 2 * Sqrt[(n-l-1)! / (n+l)!] / n^2},
	(2 r/n)^l * normFac * Exp[-r/n] * LaguerreL[n-l-1, 2l+1, 2r/n]];

hydrogenWavefunction[n_, l_, m_][r_, t_, f_] :=
	hydrogenRadialWavefunction[n, l][r] * SphericalHarmonicY[l, m, t, f];

jacobiTransformMatrix[masses_List] := Module[
	{massSums = Accumulate[masses]},
	Table[Which[
		i >= j, masses[[j]] / massSums[[i]],
		i == j-1, -1,
		True, 0
	], {i, Length[masses]}, {j, Length[masses]}]];

jacobiInverseTransformMatrix[masses_List] := Module[
	{massSums = Accumulate[masses]},
	Table[Which[
		j == Length[masses], 1,
		i <= j, masses[[j+1]] / massSums[[j+1]],
		i == j+1, -massSums[[j]] / massSums[[i]],
		True, 0
	], {i, Length[masses]}, {j, Length[masses]}]];
