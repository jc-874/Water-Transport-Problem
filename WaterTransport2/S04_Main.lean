import WaterTransport2.S03_Lexicographic

/-!
# Paper 2, Section 6: the shortest optimal length is unbounded

Reverse the reference construction to obtain a forward witness. Profile duality
turns Theorem 2 into strict domination of all strategies of length at most m+1.
Theorem 3 then gives the lower bound m+2, using Paper 1's global optimality model.
-/

namespace WaterTransport.Paper2

/-!
## Forward witness and strict comparison

Reverse the profile-construction moves and use self-adjointness to evaluate the target reward.
-/

/-- Reverse the move sequence constructing `referenceProfile`, not the profile vector itself.
If the construction is `[S_1,...,S_(m+2)]`, the witness is `[S_(m+2),...,S_1]`. -/
def witness (m : ℕ) : Strategy (Vertex m) := (referenceStrategy m).reverse

theorem witness_legal (m : ℕ) (hm : 2 ≤ m) : IsLegal (spider m) (witness m) := by
  intro S hS
  exact referenceStrategy_legal m hm S (List.mem_reverse.mp hS)

/-- Reverse-profile duality evaluates the forward witness as the pairing of p_m with the explicit weights. -/
theorem witness_value (m : ℕ) :
    run (witness m) (weights m) (root m) = pairing (referenceProfile m) (weights m) := by
  simpa [witness, reverseProfile, referenceProfile] using
    reverseProfile_duality (witness m) (weights m) (root m)

/-- Every strategy of length at most m+1 is strictly worse than the reversed reference construction. -/
theorem short_strategy_lt_witness (m : ℕ) (hm : 2 ≤ m)
    (σ : Strategy (Vertex m)) (hσ : IsLegal (spider m) σ) (hlen : σ.length ≤ m + 1) :
    run σ (weights m) (root m) < run (witness m) (weights m) (root m) := by
  rw [reverseProfile_duality, witness_value]
  apply short_profile_reward_lt m hm
  refine ⟨σ.reverse, ?_, ?_, rfl⟩
  · intro S hS; exact hσ S (List.mem_reverse.mp hS)
  · simpa using hlen

/-!
## Theorem 3 and the unbounded-length consequence

Any optimal strategy must beat the witness, so it cannot belong to the class of shorter strategies.
-/

/-- Theorem 3: every globally optimal strategy has length at least `m + 2`.
The constructed witness proves this lower bound; its global optimality is not asserted. -/
theorem optimalLength_lower_bound (m : ℕ) (hm : 2 ≤ m) :
    m + 2 ≤ optimalLength (spider m) (weights m) (weights_nonnegative m hm) (root m) := by
  obtain ⟨σ, hopt, hlen⟩ :=
    optimalLength_spec (spider m) (weights m) (weights_nonnegative m hm) (root m)
  by_contra h
  have hshort : σ.length ≤ m + 1 := by omega
  exact (not_lt_of_ge (hopt.2 (witness m) (witness_legal m hm)))
    (short_strategy_lt_witness m hm σ hopt.1 hshort)

/-- For every K, an explicit three-arm spider of maximum degree at most three has
shortest optimal length greater than K. The vertex count is allowed to increase. -/
theorem no_uniform_bound (K : ℕ) :
    ∃ m : ℕ, ∃ hm : 2 ≤ m,
      (∀ v, (spider m).degree v ≤ 3) ∧
      K < optimalLength (spider m) (weights m) (weights_nonnegative m hm) (root m) := by
  refine ⟨max 2 K, le_max_left _ _, spider_degree_le_three _, ?_⟩
  have h := optimalLength_lower_bound (max 2 K) (le_max_left _ _)
  have := le_max_right 2 K
  omega

end WaterTransport.Paper2
