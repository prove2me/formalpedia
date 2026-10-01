-- Prove2me | Theorems.Thm_syracuse_descent_eleven_steps_seven_mod32_mod524288
-- name    : syracuse_descent_eleven_steps_seven_mod32_mod524288
-- status  : Open
-- author  : @Sneed
-- created : 2026-10-01T06:09:15.642995+00:00
-- url     : https://prove2.me/theorems/1f1adb4c-a859-4930-afcf-1b7d00296ae3
-- title:
--   Eleven-step Syracuse descent on 194 residual classes modulo $2^{19}$
-- statement:
--   Let $T$ be the accelerated Syracuse map. For every natural number $n$ whose residue modulo $2^{19}=524288$ lies in the displayed 194-element set, the fixed iterate $T^{11}(n)$ is strictly smaller than $n$. These classes are the first uniformly contracting branches obtained by refining the 395 classes of `syracuse_descent_residual_seven_mod32_mod65536`: every canonical representative has a Terras certificate at 11 accelerated steps with total stripped 2-adic exponent 18, so $3^{11}<2^{18}$ and the 19-bit uniformity budget is sufficient.
-- source:
--   Exact residue refinement of Prove2Me theorem syracuse_descent_residual_seven_mod32_mod65536 (https://prove2.me/theorems/b5094e6b-1347-43fe-ac3d-adbf79509f5e), using syracuse_uniform_descent (https://prove2.me/theorems/cd79de19-4613-42b0-afc9-48de75023e4a) and exact accelerated Syracuse iteration. R. Terras, Acta Arith. 30 (1976), 241-252.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
set_option maxRecDepth 100000

theorem syracuse_descent_eleven_steps_seven_mod32_mod524288 (n : ℕ)
    (h : n % 524288 ∈ ({
          6055, 12199, 13031, 17639, 20391, 20551, 24423, 25447, 26695, 26855, 27495, 30055, 30567,
          31591, 32103, 35175, 39783, 41319, 55463, 59719, 60071, 62791, 68935, 69287, 74215,
          77127, 80999, 83431, 84071, 87143, 88167, 91751, 96359, 97895, 109287, 112359, 115431,
          116455, 116647, 120039, 124647, 125863, 126183, 133991, 136039, 140647, 151719, 154791,
          157863, 158887, 162119, 162471, 164167, 167079, 168263, 168615, 168775, 172871, 173383,
          176455, 176615, 181063, 182087, 182759, 187495, 190279, 190567, 196711, 204903, 215783,
          218855, 219047, 224999, 225191, 225351, 229447, 233191, 235367, 236903, 237639, 238663,
          239975, 243047, 244071, 244583, 246855, 252263, 258215, 261287, 267431, 270663, 272711,
          275271, 275623, 275783, 281415, 281927, 289607, 289895, 291943, 296039, 296551, 300647,
          301159, 304231, 308839, 309863, 318055, 318183, 320231, 324327, 324839, 328935, 329447,
          331847, 332519, 337127, 337991, 338151, 340839, 341863, 343399, 346183, 346343, 346471,
          346983, 352615, 360615, 360807, 362663, 366759, 367271, 371367, 371879, 374951, 379559,
          380583, 381255, 381415, 385511, 385863, 388775, 393703, 394727, 395079, 398439, 400487,
          402919, 403047, 403559, 409191, 409703, 417383, 423847, 426727, 427943, 428775, 431335,
          431847, 436135, 437159, 437479, 437991, 442439, 444263, 445351, 445671, 445799, 447335,
          447847, 451655, 451943, 457063, 460135, 469159, 471207, 473767, 474279, 477511, 479911,
          480423, 480583, 483655, 484679, 487911, 488103, 488263, 492871, 494055, 494407, 502247,
          509031, 513639, 522855
        } : Finset ℕ)) :
    syracuseStep^[11] n < n := by sorry
