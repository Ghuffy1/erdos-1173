/- Independent statement bridge. The target below is written directly from the
original problem, rather than using the construction's predicate definitions. -/
import Erdos1173

open Cardinal Ordinal Set
open scoped Cardinal Ordinal

namespace StatementAudit

def OriginalCounterexample : Prop :=
  (∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ ℵ_ o = ℵ_ (Order.succ o)) →
    ∃ f : (ω_ (ω + 1 : Ordinal.{0})).ToType → Set (ω_ (ω + 1 : Ordinal.{0})).ToType,
      (∀ a, a ∉ f a) ∧
      (∀ a, #(f a) ≤ ℵ_ ω) ∧
      (∀ a b, a ≠ b → #(f a ∩ f b : Set _) < ℵ_ ω) ∧
      (∀ Y : Set (ω_ (ω + 1 : Ordinal.{0})).ToType, #Y = ℵ_ (ω + 1) →
        ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧ b ∈ f a)

theorem original_statement_bridge : OriginalCounterexample := by
  classical
  intro h
  obtain ⟨f, hf, hn⟩ := Erdos1173.erdos_1173_counterexample h
  refine ⟨f, hf.1, hf.2.1, hf.2.2, ?_⟩
  intro Y hY
  by_contra hbad
  have hfree : Erdos1173.IsFreeSet f Y := by
    intro a ha b hb hab hmem
    exact hbad ⟨a, ha, b, hb, hab, hmem⟩
  exact hn Y hfree hY

end StatementAudit

set_option pp.universes true in
#check @Erdos1173.erdos_1173_counterexample
#check @Erdos1173.erdos_1173_negative
#check @StatementAudit.original_statement_bridge
#print Cardinal.GCH
#print Erdos1173.IsSetMapping
#print Erdos1173.IsFreeSet
#print StatementAudit.OriginalCounterexample
#print Erdos1173.erdos_1173_counterexample
#print Erdos1173.erdos_1173_negative
#print axioms Erdos1173.counterexample_isSetMapping
#print axioms Erdos1173.counterexample_no_large_free_set
#print axioms Erdos1173.erdos_1173_counterexample
#print axioms Erdos1173.erdos_1173_negative
#print axioms StatementAudit.original_statement_bridge
