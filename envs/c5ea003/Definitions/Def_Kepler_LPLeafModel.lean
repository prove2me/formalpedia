-- Prove2me | Definitions.Def_Kepler_LPLeafModel
-- name    : Kepler_LPLeafModel
-- status  : Definition
-- author  : @Minghui
-- created : 2026-09-27T03:10:59.91643+00:00
-- url     : https://prove2.me/theorems/1b723285-84da-46d9-bd72-38e1ada80cec
-- title:
--   Fixed LP selectors and strict decoding
-- statement:
--   This bundle fixes an ordered array of $216$ distinct finite Unicode row-name strings and an ordered array of $43{,}078$ pairs $(g,s)\in\mathbb N\times\mathrm{String}$ obtained by concatenating the forty fixed leaf blocks in numerical block order $0,\ldots,39$. A row selection consists of an arbitrary natural row-name index and an ordered list of natural instance indices. A leaf specification consists of a natural graph index, natural precision, Boolean direct-infeasible flag and ordered list of row selections; the record types themselves impose no validity conditions. An index character decodes exactly when its Unicode code point is between $35$ (#) and $112$ (p), inclusive, excluding $92$ (backslash); its value is the code point minus $35$, with a further subtraction of $1$ above $92$, so the possible values are $0,\ldots,76$. A mask digit is the position, numbered $0,\ldots,63$, in the alphabet A–Z, a–z, 0–9, minus sign, underscore; other characters fail. A character-list mask with digit values $d_0,\ldots,d_{k-1}$ means $\sum_{j=0}^{k-1}d_j64^j$, with the first character least significant; it succeeds only if this number is strictly below $2^{77}$, returning the increasing list of its set-bit indices among $0,\ldots,76$. The empty mask means zero and returns the empty list; arbitrarily many high-order zero digits are allowed. A selection string must have at least two characters: its first code point is $256+n$ for an in-range row-name index $0\leq n<216$, and its second character is i or b. In i mode, every remaining character is decoded as an index, preserving order and repetitions; in b mode the rest is the mask just defined. An empty payload in either mode succeeds with no indices. Any bad name, mode or payload character fails. To decode a leaf pair $(g,s)$, require a first character 3 through 7 and second character I or B, then split the remaining string at vertical bars and decode every resulting selection. The resulting specification has graph index exactly $g$, precision equal to the initial digit and direct-infeasible true exactly for I. Empty selection pieces fail, so a leaf with no selection text, leading/trailing separators or adjacent separators does not decode. No bound is checked on $g$, and selections or their indices need not be unique. The fixed template data consist of $1{,}525$ records containing a name, a standard-only Boolean, precision, an index pool, integer-coefficient feature terms and an integer right-hand side. Template lookup for a true standard flag prefers the first exact name/precision match with true standard-only flag and otherwise the first false-flag match; a false standard flag permits only false-flag matches. A precomputed array of $2{,}160$ optional templates lists this lookup first for standard false then true, within each for precisions $3,4,5,6,7$, and within each precision in row-name order. Missing matches remain empty optional entries. Selection by arbitrary flag $s$, precision $p$ and name index $n$ first requires $3\leq p\leq7$ and $n<216$, then returns the optional table entry at $((5\text{ if }s\text{ else }0)+p-3)\,216+n$; range failures or an empty entry return no template. These definitions perform parsing and lookup only and assert no row inequality, program compilation, infeasibility or certificate existence.
--
--   **Source and scope.** Primary §9; formal_lp/hypermap/lp_certificate.hl:4–30, main/prove_flyspeck_lp.hl:263–348,856–1037. Concatenates all 43,078 fixed selector records, retains 216 row names, and decodes source precision, mode and selected row indices.
-- source:
--   Hales et al. (2017), A Formal Proof of the Kepler Conjecture, https://doi.org/10.1017/fmp.2017.1; Primary §9; formal_lp/hypermap/lp_certificate.hl:4–30, main/prove_flyspeck_lp.hl:263–348,856–1037. Concatenates all 43,078 fixed selector records, retains 216 row names, and decodes source precision, mode and selected row indices.; https://github.com/flyspeck/flyspeck/tree/1ce0353008eba83d3c76ae9a25c3c242e4802d53

/-
Flyspeck source material is reproduced and adapted under this license:
MIT License

Copyright (c) 2014 Thomas C. Hales

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
SOFTWARE.

-/
import Definitions.Def_Kepler_LPRoundedTemplates
import Definitions.Def_Kepler_LPLeafData00
import Definitions.Def_Kepler_LPLeafData01
import Definitions.Def_Kepler_LPLeafData02
import Definitions.Def_Kepler_LPLeafData03
import Definitions.Def_Kepler_LPLeafData04
import Definitions.Def_Kepler_LPLeafData05
import Definitions.Def_Kepler_LPLeafData06
import Definitions.Def_Kepler_LPLeafData07
import Definitions.Def_Kepler_LPLeafData08
import Definitions.Def_Kepler_LPLeafData09
import Definitions.Def_Kepler_LPLeafData10
import Definitions.Def_Kepler_LPLeafData11
import Definitions.Def_Kepler_LPLeafData12
import Definitions.Def_Kepler_LPLeafData13
import Definitions.Def_Kepler_LPLeafData14
import Definitions.Def_Kepler_LPLeafData15
import Definitions.Def_Kepler_LPLeafData16
import Definitions.Def_Kepler_LPLeafData17
import Definitions.Def_Kepler_LPLeafData18
import Definitions.Def_Kepler_LPLeafData19
import Definitions.Def_Kepler_LPLeafData20
import Definitions.Def_Kepler_LPLeafData21
import Definitions.Def_Kepler_LPLeafData22
import Definitions.Def_Kepler_LPLeafData23
import Definitions.Def_Kepler_LPLeafData24
import Definitions.Def_Kepler_LPLeafData25
import Definitions.Def_Kepler_LPLeafData26
import Definitions.Def_Kepler_LPLeafData27
import Definitions.Def_Kepler_LPLeafData28
import Definitions.Def_Kepler_LPLeafData29
import Definitions.Def_Kepler_LPLeafData30
import Definitions.Def_Kepler_LPLeafData31
import Definitions.Def_Kepler_LPLeafData32
import Definitions.Def_Kepler_LPLeafData33
import Definitions.Def_Kepler_LPLeafData34
import Definitions.Def_Kepler_LPLeafData35
import Definitions.Def_Kepler_LPLeafData36
import Definitions.Def_Kepler_LPLeafData37
import Definitions.Def_Kepler_LPLeafData38
import Definitions.Def_Kepler_LPLeafData39

set_option autoImplicit false
set_option maxRecDepth 4096

namespace KeplerMission.SourceLP

def sourceRowNames : Array String := #[
  "RHA", "RHB", "RHBHI", "RHBLO", "azim2_hi", "azim2_lo", "azim2c", "azim2c_neg", "azim3_hi", "azim3_lo", "azim3c", "azim3c_neg", "azim_hi", "azim_lo", "azim_sum", "azim_sum_neg", "crossdiag", "edge_sym", "edge_sym_neg", "ineq0", "ineq1", "ineq10", "ineq100", "ineq101", "ineq102", "ineq103", "ineq104", "ineq105", "ineq106", "ineq107", "ineq108", "ineq109", "ineq11", "ineq110", "ineq111", "ineq112", "ineq113", "ineq114", "ineq115", "ineq116", "ineq117", "ineq118", "ineq119", "ineq12", "ineq120", "ineq13", "ineq14", "ineq15", "ineq16", "ineq17", "ineq18", "ineq19", "ineq2", "ineq20", "ineq21", "ineq22", "ineq23", "ineq24", "ineq25", "ineq26", "ineq27", "ineq28", "ineq29", "ineq3", "ineq30", "ineq31", "ineq32", "ineq33", "ineq34", "ineq35", "ineq36", "ineq37", "ineq38", "ineq39", "ineq4", "ineq40", "ineq41", "ineq42", "ineq43", "ineq44", "ineq45", "ineq46", "ineq47", "ineq48", "ineq49", "ineq5", "ineq50", "ineq51", "ineq52", "ineq53", "ineq54", "ineq55", "ineq56", "ineq57", "ineq58", "ineq59", "ineq6", "ineq60", "ineq61", "ineq62", "ineq63", "ineq64", "ineq65", "ineq66", "ineq67", "ineq68", "ineq69", "ineq7", "ineq70", "ineq73", "ineq74", "ineq75", "ineq76", "ineq77", "ineq78", "ineq79", "ineq8", "ineq80", "ineq81", "ineq82", "ineq83", "ineq84", "ineq85", "ineq86", "ineq88", "ineq89", "ineq9", "ineq90", "ineq91", "ineq92", "ineq93", "ineq94", "ineq95", "ineq96", "ineq97", "ineq98", "ineq99", "ln_def", "ln_def_neg", "ln_hi", "ln_lo", "perimZ", "rhazim2c", "rhazim3c", "rhazim_hi", "rhazim_lo", "rhazim_sum", "rhazim_sum_neg", "rho_def", "rho_def_neg", "rho_hi", "rho_lo", "sol_hi", "sol_lo", "sol_sum3", "sol_sum3_neg", "tau4", "tau5", "tau5h", "tau6", "tauB4h", "tau_hi", "tau_lo", "tau_sum3_neg", "tau_sum4", "tau_sum4_neg", "tau_sum5_neg", "tau_sum6_neg", "y1_def", "y1_def_neg", "y1_hi", "y1_lo", "y2_def", "y2_def_neg", "y2_hi", "y2_lo", "y3_def", "y3_def_neg", "y3_hi", "y3_lo", "y4_def", "y4_def_neg", "y4_hi", "y4_lo", "y5_def", "y5_def_neg", "y5_hi", "y5_lo", "y6_def", "y6_def_neg", "y6_hi", "y6_lo", "y8_def_neg", "y8_hi", "y9_def_neg", "y9_hi", "yapex_sup_flat", "ye_hi", "ye_lo", "yn_hi", "yn_lo", "yy1", "yy10", "yy11", "yy12", "yy13", "yy14", "yy15", "yy2", "yy3", "yy4", "yy5", "yy6", "yy7", "yy8", "yy9"]

/-- Every final LP leaf: archive index, then exact precision/mode/row selectors.
All 43,078 entries are fixed specification data; certificates are separate. -/
def sourceLeafCodes : Array (ℕ × String) :=
  sourceLeafBlock0 ++ sourceLeafBlock1 ++ sourceLeafBlock2 ++ sourceLeafBlock3 ++ sourceLeafBlock4 ++ sourceLeafBlock5 ++ sourceLeafBlock6 ++ sourceLeafBlock7 ++ sourceLeafBlock8 ++ sourceLeafBlock9 ++ sourceLeafBlock10 ++ sourceLeafBlock11 ++ sourceLeafBlock12 ++ sourceLeafBlock13 ++ sourceLeafBlock14 ++ sourceLeafBlock15 ++ sourceLeafBlock16 ++ sourceLeafBlock17 ++ sourceLeafBlock18 ++ sourceLeafBlock19 ++ sourceLeafBlock20 ++ sourceLeafBlock21 ++ sourceLeafBlock22 ++ sourceLeafBlock23 ++ sourceLeafBlock24 ++ sourceLeafBlock25 ++ sourceLeafBlock26 ++ sourceLeafBlock27 ++ sourceLeafBlock28 ++ sourceLeafBlock29 ++ sourceLeafBlock30 ++ sourceLeafBlock31 ++ sourceLeafBlock32 ++ sourceLeafBlock33 ++ sourceLeafBlock34 ++ sourceLeafBlock35 ++ sourceLeafBlock36 ++ sourceLeafBlock37 ++ sourceLeafBlock38 ++ sourceLeafBlock39
end KeplerMission.SourceLP


set_option autoImplicit false

namespace KeplerMission.SourceLP

structure RowSelection where
  nameIndex : ℕ
  indices : List ℕ

structure LeafSpecification where
  graphIndex : ℕ
  precision : ℕ
  directInfeasible : Bool
  selections : List RowSelection

def decodeIndexCharacter (c : Char) : Option ℕ :=
  if '#' ≤ c ∧ c ≤ 'p' ∧ c ≠ '\\' then
    some (c.toNat - 35 - if 92 < c.toNat then 1 else 0)
  else none

def decodeMaskCharacter (c : Char) : Option ℕ :=
  let alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList
  if c ∈ alphabet then some (alphabet.idxOf c) else none

/-- A bounded bit mask is a lossless encoding of the source's increasing index list. -/
def decodeMask (cs : List Char) : Option (List ℕ) := do
  let digits ← cs.mapM decodeMaskCharacter
  let mask := digits.foldr (fun digit rest => digit + 64 * rest) 0
  if mask < 2 ^ 77 then some ((List.range 77).filter mask.testBit) else none

def decodeSelection (s : String) : Option RowSelection := do
  let name :: mode :: payload := s.toList | none
  if name.toNat < 256 ∨ 256 + sourceRowNames.size ≤ name.toNat then none
  else
    let indices ← if mode = 'i' then payload.mapM decodeIndexCharacter
      else if mode = 'b' then decodeMask payload else none
    return ⟨name.toNat - 256, indices⟩

def decodeLeafSpecification (entry : ℕ × String) : Option LeafSpecification := do
  let precision :: mode :: payload := entry.2.toList | none
  if precision < '3' ∨ '7' < precision ∨ (mode ≠ 'I' ∧ mode ≠ 'B') then none
  else
    let selections ← ((String.ofList payload).splitOn "|").mapM decodeSelection
    return ⟨entry.1, precision.toNat - '0'.toNat, mode == 'I', selections⟩

/-- Precompute only the fixed source name/precision/standard lookup table. -/
def sourceTemplateTable : Array (Option RowTemplate) :=
  (#[false, true]).flatMap (fun standard =>
    (#[3, 4, 5, 6, 7]).flatMap (fun precision =>
      sourceRowNames.map (lookupTemplate standard precision)))

def selectedTemplate (standard : Bool) (precision nameIndex : ℕ) : Option RowTemplate := do
  if precision < 3 ∨ 7 < precision ∨ sourceRowNames.size ≤ nameIndex then none
  else
    let index := ((if standard then 5 else 0) + precision - 3) * sourceRowNames.size + nameIndex
    (← sourceTemplateTable[index]?)

end KeplerMission.SourceLP


