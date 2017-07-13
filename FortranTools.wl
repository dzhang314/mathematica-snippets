(* ::Package:: *)

(* :Title: FortranTools *)
(* :Context: FortranTools` *)
(* :Author: David K. Zhang *)
(* :Date: 2017-07-13 *)

(* :Package Version: 0.1 *)
(* :Wolfram Language Version: 11.0 *)

(* :Summary: FortranTools is a Wolfram Language package containing several
             utility functions for exporting data and code from the Wolfram
             language into modern Fortran dialects (90/95/2003/2006). *)

(* :Copyright: (c) 2017 David K. Zhang
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE. *)

BeginPackage["FortranTools`"];

RealString::usage = "RealString[x, d, e] returns a string containing a \
representation of x in scientific notation containing d digits after the \
decimal point and e digits in the exponent. The exponent is truncated if \
wider than e digits, so it is necessary to ensure that e is sufficiently \
large.";

FortranParameterArrayDeclaration::usage = "FortranParameterArrayDeclaration\
[arrName, arrData, d, e, k] returns a string containing Fortran code which \
delcares a real parameter array of kind k, with name arrName, containing data \
arrData. Each entry is printed in scientific notation, with d digits after the \
decimal point and e digits in the exponent. The exponent is truncated if \
wider than e digits, so it is necessary to ensure that e is sufficiently \
large. Note that Fortran arrays are stored in column-major order, so their \
indices are reversed with respect to Mathematica arrays (i.e., \
arrName(i, j, k) in Fortran corresponds to arrData[[k, j, i]] in Mathematica).";

Begin["`Private`"];

RealString[
  x_?NumericQ,
  numDecimalDigits_Integer?NonNegative,
  numExponentDigits_Integer?NonNegative
] := Block[{xPrec, digits, exponent, digitString},
  xPrec = SetPrecision[x, Infinity];
  {digits, exponent} = RealDigits[
    xPrec, 10, numDecimalDigits + 1];
  If[First[digits] === 0, exponent = 1];
  digitString = FromCharacterCode[digits + 48];
  StringJoin[
    If[xPrec < 0, "-", "+", "+"],
    StringTake[digitString, 1], ".",
    StringDrop[digitString, 1], "E",
    If[exponent <= 0, "-", "+", "+"],
    IntegerString[exponent - 1, 10, numExponentDigits]]];

FortranParameterArrayDeclaration[
  name_String,
  data_List?(ArrayQ[#, _, NumericQ] &),
  numDecimalDigits_Integer?NonNegative,
  numExponentDigits_Integer?NonNegative,
  kind_String
] := Block[{dimensionStr, dataStr},
  dimensionStr = StringJoin@Riffle[
    IntegerString /@ Reverse@Dimensions[data], ", "];
  dataStr = StringJoin@Riffle[Map[
    RealString[#, numDecimalDigits, numExponentDigits] <> "_" <> kind &,
    Flatten[data]], ", &\n    & "];
  StringJoin[
    "real(", kind, "), parameter :: ",
    name, "(", dimensionStr, ") = reshape((/ &\n",
    "    & ", dataStr, " /), &\n",
    "    & (/ ", dimensionStr, " /))"]];

End[]; (* `Private` *)
EndPackage[];