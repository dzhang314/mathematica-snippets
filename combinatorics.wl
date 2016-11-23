(* ::Package:: *)

ClearAll[orderedIntegerPartitions];

orderedIntegerPartitions[0, min_Integer][n_Integer] :=
	If[n == 0, {{}}, {}];

orderedIntegerPartitions[len_Integer, min_Integer][n_Integer] :=
orderedIntegerPartitions[len, min][n] = Join @@ Table[
	Prepend[k] /@ orderedIntegerPartitions[len - 1, min][n - k],
	{k, min, n - min*(len-1)}];


ClearAll[fullKaryTrees];

fullKaryTrees[0][v_Integer] :=
	If[v == 0, {\[FormalCapitalV][]}, {}];

fullKaryTrees[k_Integer][1] /; k > 1 = {\[FormalCapitalL]};

fullKaryTrees[k_Integer][v_Integer] /; k > 1 :=
fullKaryTrees[k][v] = Join @@ Table[
	\[FormalCapitalV] @@@ Tuples[fullKaryTrees[k] /@ part],
	{part, orderedIntegerPartitions[k, 1][v]}];


ClearAll[enumerateTree];

enumerateTree[tree_] := Block[{i = 0, j = 0},
	tree /. {\[FormalCapitalV] :> Indexed[\[FormalCapitalV], ++i], \[FormalCapitalL] :> Indexed[\[FormalCapitalL], ++j]}];


(* Generate the permutation matrix corresponding
	to a given permutation perm. *)
permutationMatrix = Compile[{{perm, _Integer, 1}},
	Module[{mat = Table[0, {Length@perm}, {Length@perm}]},
		Do[mat[[i, perm[[i]]]] = 1,
			{i, Length@perm}];
		mat]];

(* Find the set of permutations under which the list xs is invariant. *)
stabilizerSubgroup[xs_List] := Select[
	Permutations @ Range @ Length @ xs,
	xs[[#]] === xs &];

(* Count the number of elements of the list xs that
	change when the permutation perm is applied. *)
countChanges[xs_List, perm_List] := Length @ Select[
	Transpose @ {xs, xs[[perm]]}, Not @* Apply[SameQ]];
