import WaterTransport2
import WaterTransport3
import Lean
import Lean.Util.CollectAxioms

/-!
# 第二、三篇传递公理审计（只有明确列出的七个 §6 待证结论容许 sorryAx）

运行 `lake env lean AuditProgress.lean`。逐项检查传递公理依赖，拒绝自定义公理和
原生计算断言；第二篇全部声明和第三篇主体必须没有 `sorryAx`，包括私有辅助声明。
第一篇仍由 `Audit.lean` 独立执行严格零 sorry 审计，不在此降低验收要求。
文件3 §6 的三条证书上界按用户要求暂跳过，其下游结论仍标为待证。
-/

private def stableExprRepr (s : String) : String := Id.run do
  let constructors := #["Lean.Expr.forallE", "(Lean.Expr.forallE",
    "Lean.Expr.lam", "(Lean.Expr.lam", "Lean.Expr.letE", "(Lean.Expr.letE"]
  let mut previous := ""
  let mut result : Array String := #[]
  for line in s.splitOn "\n" do
    result := result.push <|
      if constructors.contains previous.trimAscii.toString &&
          (line.splitOn "«_@»").length != 1 then "Lean.Name.anonymous" else line
    previous := line
  return String.intercalate "\n" result.toList

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  let deferred := #[
    ``WaterTransport.Paper3.RepetitionExample.arbitrary_strategy_bound,
    ``WaterTransport.Paper3.RepetitionExample.repetitionFree_bound,
    ``WaterTransport.Paper3.RepetitionExample.three_step_bound,
    ``WaterTransport.Paper3.RepetitionExample.targetSup_value,
    ``WaterTransport.Paper3.RepetitionExample.witness_optimal,
    ``WaterTransport.Paper3.RepetitionExample.every_optimal_repeats,
    ``WaterTransport.Paper3.RepetitionExample.shortest_length]
  for modulePrefix in #[`WaterTransport2, `WaterTransport3] do
    let names := env.constants.fold (init := #[]) fun acc name _ =>
      match env.getModuleIdxFor? name with
      | some idx =>
        if modulePrefix.isPrefixOf env.header.moduleNames[idx.toNat]! then acc.push name else acc
      | none => acc
    if names.isEmpty then
      throwError "No declarations found in {modulePrefix}; report did not run."
    let mut pending : Nat := 0
    for name in names do
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
      if axioms.contains ``sorryAx then
        unless deferred.contains name do
          throwError "A declaration outside the seven explicitly deferred conclusions depends on sorryAx: {name}"
        pending := pending + 1
        if !isPrivateName name then
          if let some (.thmInfo _) := env.find? name then
            logInfo m!"PENDING (transitive sorryAx): {name}"
    logInfo m!"{modulePrefix}: {names.size} declarations; {pending} depend on sorryAx (only explicitly deferred certificates allowed)."

/- 重构前的 140 个公开数学声明全部保留；私有化只改变可见性。
比较完整类型和定义体，允许自动绑定变量名及 private 名称前缀变化。
基线在本次修改代码前生成；缺失时拒绝运行，不能从修改后的代码重建。 -/
open Lean Elab Command in
run_cmd do
  let file := "Research/refactor_contracts23.json"
  unless ← System.FilePath.pathExists file do
    throwError "Missing pre-refactor baseline: {file}"
  let expected ← ofExcept (Json.parse (← IO.FS.readFile file) >>=
    fromJson? (α := Array (String × String × Option String)))
  unless expected.size == 140 do
    throwError "Expected 140 original declarations"
  let env ← getEnv
  let project := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      let moduleName := env.header.moduleNames[idx.toNat]!
      if (`WaterTransport2).isPrefixOf moduleName || (`WaterTransport3).isPrefixOf moduleName
        then acc.push name else acc
    | none => acc
  let mut byUser : NameMap Name := {}
  for name in project do
    let user := privateToUserName name
    if let some previous := byUser.find? user then
      throwError "Ambiguous declaration {user}: {previous}, {name}"
    byUser := byUser.insert user name
  let normalize : Expr → String := fun e => stableExprRepr (reprStr (e.replace fun
    | .const name levels => if isPrivateName name then some (.const (privateToUserName name) levels) else none
    | _ => none))
  let localHelpers := #[
    `WaterTransport.Paper2.referenceProfile_nonnegative,
    `WaterTransport.Paper2.referenceProfile_mass,
    `WaterTransport.Paper2.referenceProfile_mem,
    `WaterTransport.Paper2.pathVertex,
    `WaterTransport.Paper3.operatorsWithin_subset,
    `WaterTransport.Paper3.RepetitionExample.edges,
    `WaterTransport.Paper3.legalMoves,
    `WaterTransport.Paper3.searchWords,
    `WaterTransport.Paper3.chooseBetter,
    `WaterTransport.Paper3.searchNodes,
    `WaterTransport.Paper3.searchWords_length,
    `WaterTransport.Paper3.searchNodes_le]
  let mut hidden : Nat := 0
  for (name, type, value) in expected do
    let some actual := byUser.find? name.toName | throwError "Missing declaration: {name}"
    let some decl := env.find? actual | throwError "Missing declaration: {actual}"
    if isPrivateName actual then
      unless localHelpers.contains name.toName do
        throwError "Paper interface is no longer public: {name}"
      hidden := hidden + 1
    unless normalize decl.type == stableExprRepr type do
      throwError "Statement changed: {name}"
    if let some original := value then
      unless decl.value?.map normalize == some (stableExprRepr original) do
        throwError "Definition changed: {name}"
  logInfo m!"Preserved all {expected.size} original Paper 2/3 statements and definitions; {hidden} local helpers now private."

/- 已补完的独立证明必须保持零 sorry；整体框架报告不能掩盖这些结论的回退。 -/
open Lean Elab Command in
run_cmd do
  let completed := #[
    ``WaterTransport.Paper2.root_barrier,
    ``WaterTransport.Paper2.root_barrier_eq,
    ``WaterTransport.Paper2.single_leaf_barrier,
    ``WaterTransport.Paper2.single_leaf_barrier_eq,
    ``WaterTransport.Paper2.double_leaf_barrier,
    ``WaterTransport.Paper2.double_leaf_barrier_eq,
    ``WaterTransport.Paper2.profile_lex_maximal,
    ``WaterTransport.Paper2.profile_length_of_comparison_eq,
    ``WaterTransport.Paper2.short_profile_reward_lt,
    ``WaterTransport.Paper2.optimalLength_lower_bound,
    ``WaterTransport.Paper2.no_uniform_bound,
    ``WaterTransport.Paper3.strategyMatrix_doublyStochastic,
    ``WaterTransport.Paper3.maxEntryNorm_mul_consensus_le,
    ``WaterTransport.Paper3.operatorPolytope_map_iso,
    ``WaterTransport.Paper3.three_noncut_vertices,
    ``WaterTransport.Paper3.nonpath_local_decomposition,
    ``WaterTransport.Paper3.ratio_near_monotone,
    ``WaterTransport.Paper3.monotone_cone_angle,
    ``WaterTransport.Paper3.path_cone_decomposition,
    ``WaterTransport.Paper3.path_strategy_totallyNonnegative,
    ``WaterTransport.Paper3.path_two_factor_decomposition,
    ``WaterTransport.Paper3.local_replacement,
    ``WaterTransport.Paper3.disconnected_window_shortening,
    ``WaterTransport.Paper3.path_variance_le_gap_energy,
    ``WaterTransport.Paper3.connected_window_energy,
    ``WaterTransport.Paper3.connected_windows_mix,
    ``WaterTransport.Paper3.uniform_convex_stabilization,
    ``WaterTransport.Paper3.operatorHull_rationalPolytope,
    ``WaterTransport.Paper3.linear_objective_attained,
    ``WaterTransport.Paper3.exactSearch_correct,
    ``WaterTransport.Paper3.uniformLength_le_explicitBound,
    ``WaterTransport.Paper3.uniformLength_asymptotic]
  for name in completed do
    for ax in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Completed theorem {name} depends on forbidden axiom {ax}"
  logInfo m!"Completed independent results: {completed.size}; standard axioms only (no sorryAx)."

#print axioms WaterTransport.Paper2.spider_degree_le_three
#print axioms WaterTransport.Paper2.referenceStrategy_legal
#print axioms WaterTransport.Paper2.weights_nonnegative
#print axioms WaterTransport.Paper2.optimalLength_lower_bound
#print axioms WaterTransport.Paper3.uniform_convex_stabilization
#print axioms WaterTransport.Paper3.RepetitionExample.witness_value
#print axioms WaterTransport.Paper3.RepetitionExample.shortest_length
#print axioms WaterTransport.Paper3.exactSearch_correct
