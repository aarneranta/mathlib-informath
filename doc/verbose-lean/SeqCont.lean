import Mathlib

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-- Continuity implies sequential continuity: the tactic proof of Massot's paper. -/
theorem seq_cont_tactic (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : sequence_tendsto u x₀)
    (hf : continuous_function_at f x₀) : sequence_tendsto (f ∘ u) (f x₀) := by
  intro ε ε_pos
  rcases hf ε ε_pos with ⟨δ, δ_pos, Hf⟩
  rcases hu δ δ_pos with ⟨N, Hu⟩
  use N
  intro n n_ge
  exact Hf (u n) (Hu n n_ge)

/-- The same proof as a term. -/
theorem seq_cont_term (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : sequence_tendsto u x₀)
    (hf : continuous_function_at f x₀) : sequence_tendsto (f ∘ u) (f x₀) :=
  fun ε ε_pos =>
    Exists.elim (hf ε ε_pos) fun δ ⟨δ_pos, Hf⟩ =>
      Exists.elim (hu δ δ_pos) fun N Hu =>
        ⟨N, fun n n_ge => Hf (u n) (Hu n n_ge)⟩

/-- Constant sequences converge. -/
theorem const_converges (u : ℕ → ℝ) (l : ℝ) (h : ∀ n, u n = l) : sequence_tendsto u l :=
  fun ε ε_pos => ⟨0, fun n _ => by rw [h n, sub_self, abs_zero]; exact le_of_lt ε_pos⟩
