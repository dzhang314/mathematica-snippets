(* ::Package:: *)

(* ::Section:: *)
(*Fortran Code Export*)


(* ::Subsection:: *)
(*Declaring Variables*)


f90form`DeclareVars::usage = "f90form`DeclareVars[attrs, varNames] returns a \
list of strings comprising the lines of a Fortran variable declaration, in \
which the variable names in varNames are declared to have the attributes in \
attrs. An attempt is made to keep the lines under 72 characters in length.";


f90form`DeclareRegisters::usage = "f90form`DeclareRegisters[type, n] returns \
a list of strings comprising the lines of a Fortran variable declaration \
for n variables of type type. The CompilePrint naming convention is used.";

f90form::tensorExperimental = "Currently, support for tensors is experimental \
in f90form. Output code will likely require human editing before use.";

f90form`DeclareRegisters[{MTensor, n_Integer}] := (
	Message[f90form::tensorExperimental];
	{});

f90form`DeclareRegisters[x_] := Throw @ StringForm[
	"Unrecognized register type ``", x];


f90form`DeclareArgument[type_Symbol, n_Integer] := f90form`DeclareVars[
	{f90form[type], "intent(in)"}, {"arg" <> ToString[n]}];

f90form`DeclareArgument[MTensor[type_Symbol, r_Integer], n_Integer] := Module[
	{colons = "(" <> riffleJoin[ConstantArray[":", r], ","] <> ")"},
	f90form`DeclareVars[{f90form[type], "intent(in)"},
		{"arg" <> ToString[n] <> colons}]];


(* ::Subsection:: *)
(*Translating Instructions*)


(* f90form -- Converting WVM control flow to Fortran control flow. *)

f90form @ Instruction["Jump", Line[n_Integer]] := "go to " <> ToString[n];

f90form @ Instruction["LoopIncr",
	{index_Register, limit_Register}, label_Integer]:=
		ToString @ StringForm["`1` = `1` + 1; if (`1` <= `2`) go to `3`",
			f90form[index], f90form[limit], f90form[label]];


(* f90form EXPERIMENTAL -- Converting WVM MTensor instructions
	to Fortran array operations. *)

f90form @ Instruction[List, {n_Integer}, dst_Register, src_List] := (
	Assert[n === Length[src]];
	Assert[Head @ First[dst] === MTensor];
	f90form[dst] <> " = [" <> riffleJoin[f90form /@ src, ", "] <> "]");

f90form @ Instruction[Table, dst_Register, dims_List] :=
	ToString @ StringForm["allocate(`1`(`2`))",
		f90form[dst], riffleJoin[f90form /@ dims, ", "]];

f90form @ Instruction[Length, dst_Register, src_] := (
	Assert[First[dst] === Integer];
	Assert[Head @ First[src] === MTensor];
	ToString @ StringForm["`1` = size(`2`)", f90form[dst], f90form[src]]);

f90form @ Instruction[Part, dst_Register, {src_, ind_}] :=
	ToString @ StringForm["`1` = `2`(`3`)",
		f90form[dst], f90form[src], f90form[ind]];

f90form @ Instruction["SetElement", dst_Register, ind_Register, src_Register] :=
	ToString @ StringForm["`1`(`2`) = `3`",
		f90form[dst], f90form[ind], f90form[src]];
