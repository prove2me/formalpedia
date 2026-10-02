-- Prove2me | Theorems.Thm_syracuse_descent_eleven_steps_seven_mod32_mod1048576
-- name    : syracuse_descent_eleven_steps_seven_mod32_mod1048576
-- status  : Proved
-- author  : @Sneed
-- created : 2026-10-01T06:09:22.448273+00:00
-- url     : https://prove2.me/theorems/ac340ba3-1df7-47f5-9db2-8b12919f873d
-- title:
--   Eleven-step Syracuse descent on 194 further residual classes modulo $2^{20}$
-- statement:
--   Let $T$ be the accelerated Syracuse map. After removing the 194 certifying classes at modulus $2^{19}$, a further 194 classes at modulus $2^{20}=1048576$ admit the fixed descent $T^{11}(n)<n$. For every canonical representative in the displayed set, the 11-step exponent sum is 19; hence $3^{11}<2^{19}$ and the 20-bit Terras uniformity budget transfers the descent to the whole arithmetic progression.
-- source:
--   Second exact residue refinement of Prove2Me theorem syracuse_descent_residual_seven_mod32_mod65536 (https://prove2.me/theorems/b5094e6b-1347-43fe-ac3d-adbf79509f5e), using syracuse_uniform_descent (https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a) and exact accelerated Syracuse iteration. R. Terras, Acta Arith. 30 (1976), 241-252.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
set_option maxRecDepth 100000

theorem syracuse_descent_eleven_steps_seven_mod32_mod1048576 (n : ℕ)
    (h : n % 1048576 ∈ ({
          5287, 8519, 10567, 13479, 13639, 19783, 27751, 29799, 33895, 39015, 42087, 56039, 58087,
          62183, 67303, 70375, 81255, 84327, 90471, 98663, 105127, 109223, 117415, 118439, 123719,
          126631, 132935, 140903, 147047, 155239, 161703, 165799, 169191, 173991, 175015, 175335,
          180295, 182119, 183207, 183527, 185191, 189511, 207015, 209063, 212135, 215367, 218279,
          218439, 221511, 222535, 225767, 230727, 231911, 240103, 246887, 275175, 292199, 294247,
          297319, 303463, 322215, 331431, 353895, 360039, 378791, 382183, 388007, 388327, 396135,
          398183, 413863, 416935, 420007, 421031, 424263, 426311, 429223, 430407, 435527, 438599,
          438759, 444903, 449639, 452711, 458855, 467047, 477927, 480999, 487143, 495335, 499047,
          502119, 505191, 506215, 514407, 537415, 543559, 551751, 558695, 562791, 570983, 572007,
          580199, 586983, 591079, 593991, 599271, 600135, 600295, 602983, 604007, 608327, 608487,
          609127, 622759, 624807, 628903, 634023, 637095, 643399, 643559, 647655, 655847, 656871,
          660583, 662631, 665063, 665703, 671847, 688871, 690919, 693991, 700135, 707943, 709991,
          714087, 719207, 722279, 735911, 742055, 750247, 750407, 756551, 775783, 784999, 792487,
          798631, 804071, 806823, 806983, 810855, 811879, 813127, 813287, 813927, 816999, 818023,
          826215, 841895, 846151, 849223, 855367, 860647, 863559, 867431, 869863, 870503, 873575,
          874599, 882791, 895719, 898791, 901863, 902887, 911079, 927079, 948903, 955047, 955207,
          959303, 967495, 968519, 976711, 1005479, 1011623, 1011783, 1015879, 1021799, 1024071,
          1025095, 1031015, 1033287, 1044647, 1047719
        } : Finset ℕ)) :
    syracuseStep^[11] n < n := by sorry
