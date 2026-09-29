-- Prove2me | Theorems.Thm_mme_alphaevolve_level4_global_graded_surplus
-- name    : mme_alphaevolve_level4_global_graded_surplus
-- status  : Open
-- author  : @37720879
-- created : 2026-09-28T09:22:20.837173+00:00
-- url     : https://prove2.me/theorems/2acc10fc-b51a-4257-98b3-4b86c9db4e0c
-- title:
--   Depth-four $CW_5$ finite surplus certificate for $\omega<2.371177$
-- statement:
--   令 $CW_5$ 为参数 $q=5$ 的 Coppersmith–Winograd 张量。存在正整数 $n$ 及一个第 4 层分级的全局提取方案 $D$，其底层使用 $8n$ 个 $CW_5$ 因子。记 $I(D)$ 为方案的输入副本数，$L(D)$ 为输出数的对数下界，$a,b,c$ 为输出矩阵乘法的三个维度。要求 $I(D)\ge 1$、$abc\ge 1$，并满足严格的有限盈余不等式
--
--   $$
--   I(D)\,7^{8n}<e^{L(D)}(abc)^{2371177/3000000}.
--   $$
--
--   该陈述把论文第 4 层组合损失分析的有理优化证书转成可供通用 CW 上界定理调用的有限提取见证。证明此子定理需要核验论文式 (11) 的证书，并把它实现为平台的 `GlobalCW.StartG` 数据；论文 v1 第 4 节称参数和验证代码仍待公开。
--
--   **Formalization Note** `StartG (8*n) 4` 表示八次幂方案的正整数倍，第二参数是递归层级；`D.inputs`、`D.logOutputs` 与 `D.a`、`D.b`、`D.c` 是平台已有定义。
-- source:
--   Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, arXiv:2608.16884v1, https://arxiv.org/html/2608.16884v1, Section 2.4 Eq. (11), Theorem 1, and Section 4 (rational verification); finite StartG interface from Prove2Me mme_global_CW_graded_start_omega_bound.

import Definitions.Def_mme_global_CW_graded_start_data
open MME MME.GlobalCW
set_option autoImplicit false

theorem mme_alphaevolve_level4_global_graded_surplus :
    ∃ (n : ℕ) (D : GlobalCW.StartG (8 * n) 4),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (((D.inputs * 7 ^ (8 * n) : ℕ) : ℝ) <
        Real.exp D.logOutputs *
          (((D.a * D.b * D.c : ℕ) : ℝ) ^ ((2371177 : ℝ) / 3000000))) := by sorry
