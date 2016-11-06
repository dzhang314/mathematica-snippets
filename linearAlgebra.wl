(* ::Package:: *)

ClearAll[randomSymmetricMatrix,
	realLDLTDecomposition, realLTSolve, realULTSolve, realULTInverse,
	complexLDLTDecomposition, complexULTInverse];

randomSymmetricMatrix = Compile[
	{{min, _Real}, {max, _Real}, {n, _Integer}},
	Module[{mat = Table[0.0, {n}, {n}]},
		Do[mat[[i,i]] = RandomReal[{min, max}],
			{i, n}];
		Do[mat[[i,j]] = mat[[j,i]] = RandomReal[{min, max}],
			{i, n}, {j, i-1}];
		mat]];

(* Computes the LDL^T factorization of a real matrix mat.
	Does not attempt pivoting, so may fail for some matrices.
	Returns L, with the diagonal entries of D appended as an extra row. *)
realLDLTDecomposition = Compile[{{mat, _Real, 2}}, Module[{
		diag = Table[0.0, {Length@mat}],
		low = Table[0.0, {Length@mat}, {Length@mat}],
		temp
	},
	Do[
		temp = 0.0;
		Do[temp += low[[i,j]] * low[[i,j]] * diag[[j]],
			{j, i-1}];
		diag[[i]] = mat[[i,i]] - temp;
		low[[i,i]] = 1.0;
		Do[
			temp = 0.0;
			Do[temp += low[[j,k]] * low[[i,k]] * diag[[k]],
				{k, 1, i-1}];
			low[[j,i]] = (mat[[j,i]] - temp) / diag[[i]],
		{j, i+1, Length@mat}],
	{i, Length@mat}];
	Append[low, diag]]];

(* Performs back substitution to solve the linear system low.x = vec,
	where low is a real lower-triangular matrix, and vec is an arbitrary
	real vector. Equivalent to LinearSolve[low, vec]. *)
realLTSolve = Compile[{{low, _Real, 2}, {vec, _Real, 1}},
	Module[{ans = Table[0.0, {Length@vec}], temp},
	Do[
		temp = 0.0;
		Do[temp += low[[m,i]] * ans[[i]],
			{i, m-1}];
		ans[[m]] = (vec[[m]] - temp) / low[[m,m]],
	{m, Length@vec}];
	ans]];

(* Performs back substitution to solve the linear system low.x = vec,
	where low is a real unit lower-triangular matrix, and vec is an
	arbitrary real vector. Equivalent to LinearSolve[low, vec]. *)
realULTSolve = Compile[{{low, _Real, 2}, {vec, _Real, 1}},
	Module[{ans = vec},
	Do[ans[[m]] -= low[[m,i]] * ans[[i]],
		{m, Length@vec}, {i, m-1}];
	ans]];

(* Inverts a real unit lower-triangular matrix.
	Equivalent to Inverse[low]. *)
realULTInverse = Compile[{{low, _Real, 2}},
	Module[{inv = Table[0.0, {Length@low}, {Length@low}]},
	Do[
		inv[[j,j]] = 1.0;
		Do[inv[[m,j]] -= low[[m,i]] * inv[[i,j]],
			{m, j+1, Length@low}, {i, j, m-1}],
	{j, Length@low}];
	inv]];

(* Computes the LDL^T factorization of a complex matrix mat.
	Does not attempt pivoting, so may fail for some matrices.
	Returns L, with the diagonal entries of D appended as an extra row. *)
complexLDLTDecomposition = Compile[{{mat, _Complex, 2}}, Module[{
		diag = Table[0.0 + 0.0I, {Length@mat}],
		low = Table[0.0 + 0.0I, {Length@mat}, {Length@mat}],
		temp
	},
	Do[
		temp = 0.0 + 0.0I;
		Do[temp += low[[i,j]] * low[[i,j]] * diag[[j]],
			{j, i-1}];
		diag[[i]] = mat[[i,i]] - temp;
		low[[i,i]] = 1.0 + 0.0I;
		Do[
			temp = 0.0 + 0.0I;
			Do[temp += low[[j,k]] * low[[i,k]] * diag[[k]],
				{k, 1, i-1}];
			low[[j,i]] = (mat[[j,i]] - temp) / diag[[i]],
		{j, i+1, Length@mat}],
	{i, Length@mat}];
	Append[low, diag]]];

(* Inverts a complex unit lower-triangular matrix.
	Equivalent to Inverse[low]. *)
complexULTInverse = Compile[{{low, _Complex, 2}},
	Module[{inv = Table[0.0 + 0.0I, {Length@low}, {Length@low}]},
	Do[
		inv[[j,j]] = 1.0 + 0.0I;
		Do[inv[[m,j]] -= low[[m,i]] * inv[[i,j]],
			{m, j+1, Length@low}, {i, j, m-1}],
	{j, Length@low}];
	inv]];
