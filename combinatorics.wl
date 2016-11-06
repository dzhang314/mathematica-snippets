(* ::Package:: *)

ClearAll[orderedIntegerPartitions];
orderedIntegerPartitions[len_Integer, min_Integer][n_Integer] :=
	orderedIntegerPartitions[len, min][n] = Join @@ Table[
		Prepend[k] /@ orderedIntegerPartitions[len - 1, min][n - k],
		{k, min, n - min*(len-1)}];

orderedIntegerPartitions[0, min_Integer][n_Integer] :=
	If[n == 0, {{}}, {}];

(* Generate the permutation matrix corresponding
	to a given permutation perm. *)
permutationMatrix = Compile[{{perm, _Integer, 1}},
	Module[{mat = Table[0, {Length@perm}, {Length@perm}]},
		Do[mat[[i, perm[[i]]]] = 1,
			{i, Length@perm}];
		mat]];

(* Find the set of permutations under which the list xs is invariant. *)
stabilizerSubgroup[xs_List] := Select[
	Permutations@Range@Length@xs,
	xs[[#]] === xs&];
