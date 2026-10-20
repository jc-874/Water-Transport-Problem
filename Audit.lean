import WaterTransport1
import Lean
import Lean.Util.CollectAxioms

/-!
# 第一篇严格验证：公理、声明保护与模型边界

运行 `lake env lean Audit.lean`。下文依次检查全部数学声明的公理依赖、
精简前的声明和定义（含现已私有化者），以及容易误改的模型边界。

## 第一篇全部声明的公理审计

按声明所属模块筛选 `WaterTransport1` 的所有定义、定理和辅助声明，
逐项检查传递公理依赖。除 Lean 的三个标准公理外，任何依赖都会报错；
这同时排除 `sorryAx`、自定义公理和原生计算断言。
模块筛选也涵盖私有辅助声明，不仅检查人工列出的主定理。
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | none => acc
    | some idx =>
      if (`WaterTransport1).isPrefixOf env.header.moduleNames[idx.toNat]! then
        acc.push name
      else acc
  if names.isEmpty then
    throwError "No WaterTransport declarations found; audit did not run."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"
  logInfo m!"Audited {names.size} WaterTransport declarations: only propext, Classical.choice, Quot.sound; no sorryAx or additional axioms."

/-!
## 原有声明保护（公开与私有）

精简前后的声明保护：比较所有原有公开声明的完整类型，以及数学定义的表达式。
这里覆盖 61 个公开定义或缩写及 162 个公开定理；上一节的公理审计还覆盖实例和私有声明。
基线由精简前通过构建和公理审计的环境生成，存于 Research。

移动模块会改变自动生成的束缚变量名中的宏作用域标签。只规范化 `forallE`、
`lam`、`letE` 的这类名称参数；束缚变量引用由 de Bruijn 索引表示，完全保留。
本轮将局部辅助声明设为 private。先在项目模块中按原用户名称唯一定位声明，
再把表达式中的项目私有常数名还原为同一用户名称；不删除这些声明的检查。
常数的用户名称、宇宙、绑定方式、量词、类型和定义体的其余部分均逐字比较。
名称映射发生歧义时直接报错，不能借私有化替换为同名的另一条结论。
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
  let file := "Research/refactor_contracts.json"
  unless ← System.FilePath.pathExists file do
    throwError "Missing pre-refactor baseline: {file}; refusing to create a new baseline."
  let old ← IO.FS.readFile file
  let expected ← ofExcept (Json.parse old >>=
    fromJson? (α := Array (String × String × Option String)))
  unless expected.size == 223 do
    throwError "Invalid baseline: expected 223 original mathematical declarations."
  let env ← getEnv
  -- 论文对象及结论必须仍能用原公开名称访问；不能只藏在私有证明中。
  let core := #[`WaterTransport.State, `WaterTransport.Nonnegative,
    `WaterTransport.IsLegalMove, `WaterTransport.mean, `WaterTransport.average,
    `WaterTransport.averageLinear, `WaterTransport.mass, `WaterTransport.energy,
    `WaterTransport.Strategy, `WaterTransport.IsLegal, `WaterTransport.run,
    `WaterTransport.OneStep, `WaterTransport.Reachable, `WaterTransport.reachableSet,
    `WaterTransport.RepetitionFree, `WaterTransport.IsOptimalFor, `WaterTransport.IsOptimal,
    `WaterTransport.horizonStates, `WaterTransport.horizonValues, `WaterTransport.horizonMax,
    `WaterTransport.energy_average_le, `WaterTransport.oneStep_sequence_converges,
    `WaterTransport.optimalValue, `WaterTransport.targetSup,
    `WaterTransport.optimalValue_continuousOn, `WaterTransport.continuous_objective_attained,
    `WaterTransport.target_attained, `WaterTransport.exists_optimal,
    `WaterTransport.optimalLength, `WaterTransport.pathInterval,
    `WaterTransport.endpoint_optimalLength_le_one, `WaterTransport.path_optimalLength_le_two,
    `WaterTransport.path_exists_optimal_two, `WaterTransport.path_horizon_stabilizes,
    `WaterTransport.path_targetSup_eq_horizon_two, `WaterTransport.star,
    `WaterTransport.IsGreedyLeafOrder, `WaterTransport.starGreedyStrategy,
    `WaterTransport.starGreedyStrategy_optimal, `WaterTransport.star_optimalLength_le,
    `WaterTransport.Examples.pathWeights, `WaterTransport.Examples.pathWitness,
    `WaterTransport.Examples.path_optimum, `WaterTransport.Examples.path_two_steps_necessary,
    `WaterTransport.Examples.pathWitness_first_decreases, `WaterTransport.Examples.spiderGraph,
    `WaterTransport.Examples.spiderWeights, `WaterTransport.Examples.spiderWitness,
    `WaterTransport.Examples.spider_four_steps_beat_three,
    `WaterTransport.Examples.spider_optimalLength_gt_three,
    `WaterTransport.Examples.rewardWeights, `WaterTransport.Examples.reward,
    `WaterTransport.Examples.rewardWitness, `WaterTransport.Examples.rewardWitness_optimal,
    `WaterTransport.Examples.optimal_reward_requires_repetition]
  for name in core do
    unless env.contains name do
      throwError "Paper interface is no longer public: {name}"
  logInfo m!"All {core.size} paper definitions and conclusions remain publicly accessible."
  let project := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if (`WaterTransport1).isPrefixOf env.header.moduleNames[idx.toNat]! then
        acc.push name
      else acc
    | none => acc
  let mut byUser : NameMap Name := {}
  let mut privateNames : NameMap Name := {}
  for name in project do
    let user := privateToUserName name
    if let some previous := byUser.find? user then
      throwError "Ambiguous declaration name {user}: {previous}, {name}"
    byUser := byUser.insert user name
    if isPrivateName name then
      privateNames := privateNames.insert name user
  let normalize : Expr → String := fun e => stableExprRepr (reprStr (e.replace fun
    | .const name levels => (privateNames.find? name).map (fun user => .const user levels)
    | _ => none))
  let mut hidden : Nat := 0
  for (name, type, value) in expected do
    let some actual := byUser.find? name.toName
      | throwError "Missing declaration: {name}"
    let some decl := env.find? actual
      | throwError "Missing declaration: {actual}"
    if isPrivateName actual then hidden := hidden + 1
    unless normalize decl.type == stableExprRepr type do
      throwError "Statement changed: {name}"
    if let some original := value then
      unless decl.value?.map normalize == some (stableExprRepr original) do
        throwError "Definition changed: {name}"
  logInfo m!"Preserved all {expected.size} original statements and definitions, including {hidden} now private (modulo generated binder names and private name prefixes)."

/-!
## 模型边界核对

这些检查针对本次重构最容易改变的语义：非法空操作、合法零步策略、
有限 horizon 的“至多”含义、常数状态、实际例子的执行顺序。
本文件不用 sorry；末尾公理输出应不包含 sorryAx。
-/

namespace WaterTransport.SemanticChecks

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem empty_move_illegal (G : SimpleGraph V) : ¬ IsLegalMove G ∅ := by
  simp [IsLegalMove]

theorem zero_steps_reachable (G : SimpleGraph V) (w : State V) : Reachable G w w :=
  reachable_refl G w

/-- 任意实值初态（含负值）在零步 horizon 下只有自己的目标值。 -/
theorem horizon_zero (G : SimpleGraph V) (w : State V) (x : V) :
    horizonMax G w x 0 = w x := by
  obtain ⟨σ, _, hlen, hval⟩ := horizonMax_attained G w x 0
  have hnil : σ = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
  simpa only [hnil, run_nil] using hval.symm

theorem constant_run (σ : Strategy V) (c : ℝ) : run σ (fun _ => c) = fun _ => c := by
  induction σ with
  | nil => rfl
  | cons S σ ih => simpa only [run_cons, average_const] using ih

/-- 恒定状态下，零步确实满足全局最优性定义。 -/
theorem constant_nil_optimal (G : SimpleGraph V) (c : ℝ) (x : V) :
    IsOptimal G (fun _ => c) x [] := by
  refine ⟨isLegal_nil G, ?_⟩
  intro σ _
  change run σ (fun _ => c) x ≤ c
  simp only [constant_run, le_refl]

/-- 第一篇真实两步例子：两次完整平均按时间顺序执行得到 7。 -/
theorem chronological_example : run Examples.pathWitness Examples.pathWeights 2 = 7 :=
  Examples.pathWitness_value

/-- 原图中的两点可达不足以使选集合法：路径两端跳过中点不能平均。 -/
theorem skipped_middle_illegal :
    ¬ IsLegalMove (SimpleGraph.pathGraph 3) ({0, 2} : Finset (Fin 3)) := by
  rw [path_legal_iff_interval]
  decide +kernel

/-- hw 是命题证明参数；换一份非负性证明不会改变最短长度。 -/
theorem optimalLength_proof_independent (G : SimpleGraph V) (w : State V)
    (h₁ h₂ : Nonnegative w) (x : V) :
    optimalLength G w h₁ x = optimalLength G w h₂ x := rfl

/-- 直接以非负锥为定义域，也能应用 Theorem 2.1；无需锥外连续延拓。 -/
theorem cone_objective_attained (G : SimpleGraph V)
    (f : {w : State V // Nonnegative w} → ℝ) (hf : Continuous f)
    (w : State V) (hw : Nonnegative w) :
    ∃ σ, IsLegal G σ ∧ ∀ τ, IsLegal G τ →
      f ⟨run τ w, run_nonnegative τ hw⟩ ≤ f ⟨run σ w, run_nonnegative σ hw⟩ := by
  classical
  let F : State V → ℝ := fun u => if h : Nonnegative u then f ⟨u, h⟩ else 0
  have hF : ContinuousOn F {u | Nonnegative u} := by
    apply continuousOn_iff_continuous_restrict.mpr
    have he : ({u : State V | Nonnegative u}.restrict F) = f := by
      funext u
      change F u.val = f u
      dsimp only [F]
      rw [dif_pos (show Nonnegative u.val from u.property)]
      exact congrArg f (Subtype.ext rfl)
    rw [he]
    exact hf
  obtain ⟨σ, hσ, hmax⟩ := exists_optimalFor G F hF w hw
  refine ⟨σ, hσ, fun τ hτ => ?_⟩
  simpa only [F, dif_pos (run_nonnegative τ hw), dif_pos (run_nonnegative σ hw)]
    using hmax τ hτ

/-- 忽略单点重复没有弱化例 4.3：字面上完全不重复的策略也不可能最优。 -/
theorem literal_repetition_required (σ : Strategy (Fin 4))
    (hopt : IsOptimalFor (star 3) Examples.reward Examples.rewardWeights σ) :
    ¬ σ.Nodup := by
  intro h
  exact Examples.optimal_reward_requires_repetition σ hopt (List.Nodup.filter _ h)

end WaterTransport.SemanticChecks

#print axioms WaterTransport.SemanticChecks.empty_move_illegal
#print axioms WaterTransport.SemanticChecks.zero_steps_reachable
#print axioms WaterTransport.SemanticChecks.horizon_zero
#print axioms WaterTransport.SemanticChecks.constant_run
#print axioms WaterTransport.SemanticChecks.constant_nil_optimal
#print axioms WaterTransport.SemanticChecks.chronological_example
#print axioms WaterTransport.SemanticChecks.skipped_middle_illegal
#print axioms WaterTransport.SemanticChecks.optimalLength_proof_independent
#print axioms WaterTransport.SemanticChecks.cone_objective_attained
#print axioms WaterTransport.SemanticChecks.literal_repetition_required
