(* ::Package:: *)

ClearAll[deletePairs, dualMultiplicationTable, dualMultiplicationData];

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

ClearAll[dualNumber];

Plus[dualNumber[xs___], dualNumber[ys___]] ^:=
	dualNumber @@ ({xs} + {ys}) /;
	Length[{xs}] === Length[{ys}];

Times[dualNumber[xs___], dualNumber[ys___]] ^:=
	Module[{x = {xs}, y = {ys}, n = Floor@Log2@Length[{xs}]},
		dualNumber @@ Map[Total[x[[#1]] * y[[#2]]& @@@
			dualMultiplicationData[n][#]]&, Range[2^n]]] /;
	Length[{xs}] === Length[{ys}];
