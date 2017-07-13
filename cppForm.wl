(* ::Package:: *)

Import@FileNameJoin[{$snippetDirectory, "stringHelpers.wl"}];
ClearAll[cppForm];


(* ::Section:: *)
(*WVM Types*)


cppForm[Boolean] = "bool";
cppForm[Integer] = "int";
cppForm[Real]    = "double";
cppForm[Complex] = "std::complex<double>";

cppForm`abbrev[Boolean] = "B";
cppForm`abbrev[Integer] = "I";
cppForm`abbrev[Real]    = "R";
cppForm`abbrev[Complex] = "C";
cppForm`abbrev[type_] := Throw@StringForm[
	"Unrecognized variable type ``", type];


(* ::Section:: *)
(*WVM Constants to C++ Literals*)


cppForm[n_Integer] := ToString[n];
cppForm[x_Real] := ToString@CForm[x];


(* ::Section:: *)
(*WVM Registers and Arguments*)


cppForm@Register[type_Symbol, n_Integer] :=
	cppForm`abbrev[type] <> ToString[n];
cppForm@Register[MTensor[type_Symbol, m_Integer], n_Integer] :=
	ToString@StringForm["T_`1``2`_`3`", cppForm`abbrev[type], m, n];
cppForm@Register[regType_, args___] := Throw@StringForm[
	"Unrecognized register type `1`", regType];

cppForm@Argument[n_Integer] := "arg" <> ToString[n];


(* ::Section:: *)
(*WVM Assignment*)


cppForm@Instruction[Set, dst_Register, src_Argument] :=
	cppForm[dst] <> " = arg" <> ToString@First[src] <> ";";
cppForm@Instruction[Set, dst_Register, src_] :=
	ToString@StringForm["`1` = `2`;", cppForm[dst], cppForm[src]];


(* ::Section:: *)
(*Single-argument WVM Instructions*)


cppForm@Instruction[Minus, dst_Register, {src_}] :=
	ToString@StringForm["`1` = -`2`;", cppForm[dst], cppForm[src]];
cppForm@Instruction["Reciprocal", dst_Register, {src_}] :=
	ToString@StringForm["`1` = 1.0 / `2`;", cppForm[dst], cppForm[src]];
cppForm@Instruction[Exp, dst_Register, {src_}] :=
	ToString@StringForm["`1` = exp(`2`);", cppForm[dst], cppForm[src]];
cppForm@Instruction[Gamma, dst_Register, {src_}] :=
	ToString@StringForm["`1` = tgamma(`2`);", cppForm[dst], cppForm[src]];
cppForm@Instruction[Square, dst_Register, {src_}] :=
	ToString@StringForm["`1` = `2` * `2`;", cppForm[dst], cppForm[src]];
cppForm@Instruction[Sqrt, dst_Register, {src_}] :=
	ToString@StringForm["`1` = sqrt(`2`);", cppForm[dst], cppForm[src]];
cppForm@Instruction[Internal`ReciprocalSqrt, dst_Register, {src_}] :=
	ToString@StringForm["`1` = 1.0 / sqrt(`2`);", cppForm[dst], cppForm[src]];


(* ::Section:: *)
(*Multi-argument WVM Instructions*)


cppForm@Instruction[Power, dst_Register, {base_, power_}] :=
	ToString@StringForm["`1` = pow(`2`, `3`);",
		cppForm[dst], cppForm[base], cppForm[power]];

cppForm@Instruction[Plus, dst_Register, args_List] :=
	cppForm[dst] <> " = " <> riffleJoin[cppForm /@ args, " + "] <> ";";
cppForm@Instruction[Times, dst_Register, args_List] :=
	cppForm[dst] <> " = " <> riffleJoin[cppForm /@ args, " * "] <> ";";


(* ::Section:: *)
(*WVM Tensor Instructions [[EXPERIMENTAL]]*)


cppForm@Instruction[Part, dst_Register, {src_, ind_}] :=
	ToString@StringForm["`1` = `2`[`3`];",
		cppForm[dst], cppForm[src], cppForm[ind]];
cppForm@Instruction["SetElement", dst_Register, ind_Register, src_Register] :=
	ToString@StringForm["`1`[`2`] = `3`;",
		cppForm[dst], cppForm[ind], cppForm[src]];


(* ::Section:: *)
(*Unpacking CompiledProcedure Objects*)


cppForm@CompiledSetup[instrs_List] := riffleJoin[cppForm /@ instrs, "\n"];
cppForm@CompiledConstants[instrs_List] := riffleJoin[cppForm /@ instrs, "\n"];
cppForm@CompiledInfo[argTypes_List, regTypes_List, opts___] := Module[{
	argList = riffleJoin[MapIndexed[cppForm[#1] <> " arg" <> ToString@First[#2] &,
		argTypes], ", "],
	regLines = riffleJoin[Table[
		cppForm[First@p] <> " " <> riffleJoin[
			cppForm`abbrev[First@p] <> ToString[#] & /@ Range[0, Last@p - 1], ", "
		] <> ";",
		{p, Select[regTypes, (First[#] =!= MTensor) && (Last[#] =!= 0) &]}], "\n"]
	},
	"void FUNCTION_NAME" <> "(" <> argList <> ") {" <> "\n" <> regLines];
cppForm@CompiledProcedure[ci_CompiledInfo, cs_CompiledSetup, cc_CompiledConstants,
		cr_CompiledResult, instrs_List, bytecode_List] := StringJoin[
	cppForm[ci], "\n\n",
	cppForm[cs], "\n\n",
	cppForm[cc], "\n\n",
	riffleJoin[ToString /@ cppForm /@ instrs, "\n"], "\n}"];
cppForm[cf_CompiledFunction] := cppForm@ToCompiledProcedure[cf];


(* ::Section:: *)
(*Clang-Format*)


clangFormat[code_String] := RunProcess[{"clang-format",
		"-style=\"{BasedOnStyle: Google, IndentWidth: 4}\""},
	"StandardOutput", code];

clangFormat`NoColumnLimit[code_String] := RunProcess[{"clang-format",
		"-style=\"{BasedOnStyle: Google, IndentWidth: 4, ColumnLimit: 0}\""},
	"StandardOutput", code];
