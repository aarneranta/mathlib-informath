
-- the paper's first example, as an ordinary Lean tactic proof
#verbalize "Continuity implies sequential continuity"
theorem seq_cont (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : u converges to x₀)
    (hf : f is continuous at x₀) : (f ∘ u) converges to f x₀ := by
  intro ε ε_pos
  rcases hf ε ε_pos with ⟨δ, δ_pos, Hf⟩
  rcases hu δ δ_pos with ⟨N, Hu⟩
  use N
  intro n n_ge
  exact Hf (u n) (Hu n n_ge)

#verbalize "Constant sequences converge."
theorem const_conv (u : ℕ → ℝ) (l : ℝ) (h : ∀ n, u n = l) : u converges to l := by
  intro ε ε_pos
  use 0
  intro n n_ge
  rw [h n, sub_self, abs_zero]
  exact le_of_lt ε_pos

#verbalize "Squeeze: the lower half"
theorem squeeze_low (u v : ℕ → ℝ) (l ε : ℝ) (N n : ℕ) (hN : ∀ n ≥ N, |u n - l| ≤ ε)
    (h : ∀ n, u n ≤ v n) (hn : n ≥ N) : -ε ≤ v n - l := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp (hN n hn)
  linarith [h n]
