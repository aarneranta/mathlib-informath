import Mathlib

theorem F1 (f : ℝ → ℝ) (u : ℕ → ℝ) (x0 : ℝ) (h : ∀ eps > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x0| ≤ eps) :
  ∀ eps > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x0| ≤ eps := h
theorem F2 (f : ℝ → ℝ) (x0 eps delta : ℝ) (h : delta > 0 ∧ ∀ x, |x - x0| ≤ delta → |f x - f x0| ≤ eps) :
  delta > 0 ∧ ∀ x, |x - x0| ≤ delta → |f x - f x0| ≤ eps := h
theorem F3 (u : ℕ → ℝ) (x0 delta : ℝ) (N : ℕ) (h : ∀ n ≥ N, |u n - x0| ≤ delta) :
  ∀ n ≥ N, |u n - x0| ≤ delta := h
