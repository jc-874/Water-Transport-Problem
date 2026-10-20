import WaterTransport1

/-!
本文件用固定的本地 mathlib 版本核对依赖名：
  lake env lean MathlibInventory.lean
它不含项目待证明定理；#check 不是重新证明，而是确认已有 API 的类型。
-/

#check SimpleGraph
#check SimpleGraph.induce
#check SimpleGraph.Connected
#check SimpleGraph.ConnectedComponent
#check SimpleGraph.pathGraph
#check SimpleGraph.pathGraph_adj
#check SimpleGraph.pathGraph_connected
#check SimpleGraph.starGraph
#check SimpleGraph.starGraph_adj
#check SimpleGraph.connected_starGraph
#check Finset.expect_eq_sum_div_card
#check Finset.expect_add_distrib
#check Finset.le_expect
#check Finset.expect_le
#check List.finite_length_le
#check Set.Nonempty.csSup_mem
#check Set.countable_range
#check Finset.sum_mul_sq_le_sq_mul_sq
#check LinearMap.continuous_of_finiteDimensional
#check LipschitzWith.continuous
#check IsCompact.tendsto_subseq
#check IsCompact.uniformContinuousOn_of_continuous
#check IsCompact.exists_isMaxOn
#check le_csSup
#check csSup_le
#check exists_maximal_of_chains_bounded
#check zorn_le₀
#check Nat.find_spec
#check Nat.find_min'
