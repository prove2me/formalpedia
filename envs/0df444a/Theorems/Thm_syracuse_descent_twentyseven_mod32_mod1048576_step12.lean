-- Prove2me | Theorems.Thm_syracuse_descent_twentyseven_mod32_mod1048576_step12
-- name    : syracuse_descent_twentyseven_mod32_mod1048576_step12
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T11:16:27.944975+00:00
-- url     : https://prove2.me/theorems/ed054f9e-c889-420c-812b-c6d8e2341b20
-- title:
--   Uniform twelve-step Syracuse descent on 525 twentyseven-branch progressions modulo $2^{20}$
-- statement:
--   Let $T(n)$ be the odd part of $3n+1$ (the platform's Syracuse map `syracuseStep`), and let $T^{12}$ denote twelve successive applications. Let $R$ be the explicit list of 525 distinct residues modulo $2^{20}=1048576$ enumerated in the formal statement. For every natural number $n$,
--
--   $$
--   n\bmod 1048576\in R\quad\Longrightarrow\quad T^{12}(n)<n.
--   $$
--
--   This is a uniform statement on 525 infinite arithmetic progressions, not a check of their least representatives only. Every listed residue $r$ satisfies $r\equiv 27\pmod{32}$ and lies in a class left open by the [twentyseven-branch residual descent theorem modulo $2^{18}$](https://prove2.me/theorems/bcbfb4d5-ae6b-4b5f-9022-a71426797d08): the list consists of exactly those of the $4\cdot 1386=5544$ lifts modulo $2^{20}$ of its 1386 surviving classes that admit a descent certificate with exponent budget $20$. None of these classes is certifiable at modulus $2^{18}$ or $2^{19}$.
--
--   **Method.** For each $r\in R$ the first eleven Syracuse steps of $r$ are exact rows $3b_i+1=2^{a_i}b_{i+1}$ with $b_0=r$ and odd $b_{i+1}$, with $S=\sum_{i<11}a_i\le 20$, and the twelfth row is closed by a divisor exponent $e=\min(v_2(3b_{11}+1),\,20-S)$ with quotient $B=(3b_{11}+1)/2^e<r$. The published theorem [`CollatzFrontier.syracuse_terminal_budget_of_descent`](https://prove2.me/theorems/2513a4d3-77eb-4b93-9876-33755812122c) (residue-class descent from a truncated terminal divisor) then gives $T^{12}(r+2^{20}q)<r+2^{20}q$ for all $q$. For 250 of the residues the terminal exponent is the full valuation; the other 275 need the truncated terminal row and would not be certified at modulus $2^{20}$ by an exact twelve-row certificate.
--
--   **Role.** Together with the refined residual `syracuse_descent_residual_twentyseven_mod32_mod1048576` this proves the parent residual by a case split on $n\bmod 2^{20}\in R$; it removes the fraction $525/5544\approx 0.095$ of the parent's open classes.
--
--   **Formalization Note.** The map is the existing definition `syracuseStep`; the residue list is a literal `List ℕ` inside the theorem's type, as in the modulus-$2^{18}$ list theorem [`syracuse_descent_progressions_mod262144`](https://prove2.me/theorems/b4cf0c47-c078-4235-b853-32b5a518517e). The recursion-depth option only supports elaboration of the long literal. No monotonicity of the Syracuse map is asserted.
-- source:
--   Original computation of this contribution (explicit certified refinement of https://prove2.me/theorems/bcbfb4d5-ae6b-4b5f-9022-a71426797d08 from modulus 2^18 to 2^20; the residue table is computed, not quoted from the literature). Method: residue-class descent via the Proved theorem CollatzFrontier.syracuse_terminal_budget_of_descent, https://prove2.me/theorems/2513a4d3-77eb-4b93-9876-33755812122c; exact Syracuse definition https://prove2.me/theorems/2d5fcb43-85b2-4d75-beb8-3e236e66eac3. Packaging follows the modulus-2^18 refinement syracuse_descent_progressions_mod262144, https://prove2.me/theorems/b4cf0c47-c078-4235-b853-32b5a518517e.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

set_option maxRecDepth 16384

theorem syracuse_descent_twentyseven_mod32_mod1048576_step12 (n : ℕ)
    (h : n % 1048576 ∈ ([763, 2139, 5211, 6235, 7707, 8283, 11355, 11803, 12379, 14587, 17499, 19995, 20571, 21019, 26875,
      27035, 29211, 31131, 33819, 35867, 35995, 39323, 39963, 40091, 40347, 43003, 44059, 46107,
      46875, 47899, 48283, 48539, 49147, 49179, 49307, 49947, 51995, 53019, 55323, 57339, 57499,
      58139, 62107, 64155, 68251, 71771, 72347, 73819, 74395, 77467, 77915, 83035, 83227, 83611,
      86107, 87323, 90395, 91419, 92411, 92571, 93467, 96539, 96667, 97563, 102683, 103451, 104859,
      105755, 105883, 106523, 109595, 111195, 111643, 114075, 114715, 115291, 119387, 120859,
      124507, 125531, 131739, 133723, 133883, 134811, 137883, 139931, 140027, 143003, 146971,
      149147, 153115, 156955, 159003, 159259, 163099, 167771, 168219, 168475, 171291, 171867,
      175259, 175963, 181083, 181403, 182107, 184923, 186139, 187163, 187547, 188187, 190299,
      190459, 191067, 191227, 191259, 194331, 195355, 196603, 196763, 197403, 199259, 199419,
      200475, 201499, 205563, 209691, 213083, 221435, 224507, 224795, 225371, 228603, 229627,
      231835, 232699, 234011, 237979, 238843, 241499, 244123, 247035, 247643, 247803, 250907,
      253083, 253339, 253979, 255771, 255835, 255995, 257051, 257819, 258075, 259867, 260891,
      262139, 262299, 262939, 266011, 266267, 267035, 275227, 279195, 282267, 285339, 286363,
      290907, 294555, 295163, 298235, 298267, 304379, 309659, 310555, 312347, 312571, 314395,
      316443, 318875, 319515, 322587, 323611, 331803, 332379, 338523, 338683, 340635, 342683,
      342779, 344731, 347803, 350875, 350971, 351899, 351995, 360091, 360187, 376091, 388955,
      389723, 395099, 395259, 397915, 399355, 402203, 404059, 404219, 405275, 407547, 408315,
      408571, 414491, 416507, 416763, 417531, 419931, 423003, 425723, 427099, 428123, 430331,
      431195, 432379, 436475, 437339, 440571, 442619, 445531, 445691, 446299, 451611, 451835,
      454491, 455707, 458779, 459803, 460635, 460795, 461851, 464891, 464923, 465947, 466715,
      470811, 471067, 473083, 474107, 474139, 479899, 480027, 482299, 483995, 487067, 488091,
      490139, 493211, 493659, 494235, 496731, 499355, 499963, 502427, 502875, 503035, 505115,
      506107, 508155, 508187, 511067, 511227, 512283, 513307, 516379, 517371, 522523, 525339,
      527387, 530715, 531483, 536603, 537179, 539675, 541275, 543483, 549467, 549627, 550491,
      553627, 555675, 555771, 558683, 559771, 564763, 564891, 564987, 567963, 568859, 572955,
      578075, 578843, 579099, 581915, 587291, 588059, 593051, 593755, 596251, 597147, 597851,
      600059, 601243, 602715, 605979, 606043, 606203, 606363, 606811, 607067, 607387, 609051,
      610075, 612347, 614171, 615003, 615259, 615579, 616027, 617243, 621307, 621563, 624219,
      628827, 630523, 630875, 634971, 638491, 639067, 641115, 644187, 644635, 647419, 649627,
      650331, 650491, 652827, 653563, 653723, 654587, 657819, 659291, 662779, 662939, 663387,
      663963, 666651, 666779, 671579, 672155, 672603, 672923, 677883, 678939, 679707, 680795,
      681115, 682779, 687099, 694939, 698459, 701531, 704603, 706651, 707227, 708859, 709723,
      710907, 712955, 714011, 715867, 716027, 716059, 719099, 720123, 720155, 723355, 724251,
      726299, 728315, 729371, 729499, 735515, 737691, 741979, 744475, 748123, 754267, 763483,
      772763, 783643, 785947, 786715, 789787, 791835, 792091, 794907, 798555, 801051, 804699,
      810843, 814235, 816923, 817947, 819803, 819995, 820059, 820379, 824091, 828187, 829019,
      830235, 843291, 845915, 848123, 848987, 851483, 852059, 852219, 853083, 855291, 856315,
      857627, 858363, 861275, 861435, 862459, 867579, 870651, 870811, 871579, 873499, 876379,
      876571, 876955, 879771, 880667, 881691, 884763, 885595, 885915, 887579, 890907, 893723,
      895771, 899099, 901787, 904859, 907355, 908955, 909403, 909979, 911451, 913051, 914523,
      917595, 918619, 919195, 921851, 923899, 926811, 927387, 927995, 928155, 931099, 933115,
      934171, 936187, 936347, 937243, 938267, 942491, 946459, 947227, 950299, 956443, 961275,
      964635, 965371, 969467, 974587, 975515, 975611, 978587, 983803, 984731, 990747, 992539,
      992923, 994587, 994843, 996635, 999707, 1002779, 1003035, 1003803, 1004059, 1011995, 1012251,
      1017851, 1019035, 1021947, 1023131, 1026043, 1027867, 1031163, 1031323, 1032187, 1032347,
      1035003, 1035035, 1036059, 1040379, 1040539, 1041147, 1041179, 1046619] : List ℕ)) :
    syracuseStep^[12] n < n := by sorry
