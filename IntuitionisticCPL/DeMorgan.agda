-- Constructive Provability Logic 
-- The intuitionistic, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- de Morgan laws (2 of 4 hold, the other two have a class of countermodels)

module IntuitionisticCPL.DeMorgan where
open import Prelude hiding (⊥ ; ¬)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import IntuitionisticCPL.Core
open import IntuitionisticCPL.Sequent
open import IntuitionisticCPL.Equiv
open import IntuitionisticCPL.Hilbert

module DEMORGAN (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open PROPERTIES UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF
   open EQUIV UWF

   demorgan1 : ∀{Γ A w} 
      → Empty Γ w 
      → Equiv (DecideA-InCPL Γ A w) (Γ ⇒ ¬ (□ A) ⊃ ◇ (¬ A) [ w ])
   demorgan1 {Γ} {A} {w} emp = forward , back2 
    where 
      forward : DecideA-InCPL Γ A w → Γ ⇒ ¬ (□ A) ⊃ ◇ (¬ A) [ w ]
      forward (Inl D) = ⊃R (⊃L Z (□R 
         λ ω → wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (D ω)) (⊥L Z))
      forward (Inr (w , ω , D⊥)) = 
         ⊃R (◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D⊥))

      back0 : ¬ (□ A) at w :: Γ ⇒ □ A [ w ] → DecideA-InCPL Γ A w
      back0 (□R D) = Inl (λ ω → wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω))
      back0 (⊃L Z D _) = back0 D
      back0 (⊃L (S n) _ _) = abort (emp n)
      back0 (⊥L (S n)) = abort (emp n)
      back0 (◇L (S n) _) = abort (emp n)
      back0 (□L (S n) _) = abort (emp n)
      back0 (¬◇L (S n) _) = abort (emp n)
      back0 (¬□L (S n) _) = abort (emp n)

      back1 : ¬ (□ A) at w :: Γ ⇒ ◇ (¬ A) [ w ] → DecideA-InCPL Γ A w
      back1 (⊃L Z D _) = back0 D
      back1 (◇R ω D⊥) = Inr (_ , ω , wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D⊥)
      back1 (⊃L (S n) _ _) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇L (S n) _) = abort (emp n)
      back1 (□L (S n) _) = abort (emp n)
      back1 (¬◇L (S n) _) = abort (emp n)
      back1 (¬□L (S n) _) = abort (emp n)

      back2 : Γ ⇒ ¬ (□ A) ⊃ ◇ (¬ A) [ w ] → DecideA-InCPL Γ A w
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n)

   demorgan2 : ∀{Γ A w} → Con Γ w → Γ ⇒ ◇ (¬ A) ⊃ ¬ (□ A) [ w ]
   demorgan2 con = ⊃R (◇L Z 
      λ ω D⊥ → ⊃R (□L Z 
      λ D → abort (con ω (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (nd→seq 
       (⊃E (seq→nd D⊥) 
        (seq→nd (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω)))))))))

   demorgan3 : ∀{Γ A w}
            → Empty Γ w
            → Equiv (Decide¬A-InCPL Γ A w) (Γ ⇒ ¬ (◇ A) ⊃ □ (¬ A) [ w ])
   demorgan3 {Γ} {A} {w} emp = forward , back2
    where
      forward : (Decide¬A-InCPL Γ A w) → (Γ ⇒ ¬ (◇ A) ⊃ □ (¬ A) [ w ])
      forward (Inl D⊥) = 
         ⊃R (□R (λ ω → wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (D⊥ ω)))
      forward (Inr (w₀ , ω , D)) = 
         ⊃R (⊃L Z (◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D)) (⊥L Z))

      back : (◇ A ⊃ ⊥) at w :: Γ ⇒ ◇ A [ w ] → Decide¬A-InCPL Γ A w
      back (⊃L Z D _) = back D
      back (⊃L (S n) _ _) = abort (emp n)
      back (⊥L (S n)) = abort (emp n)
      back (◇R ω D) = Inr (_ , ω , wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D)
      back (◇L (S n) _) = abort (emp n)
      back (□L (S n) _) = abort (emp n)
      back (¬◇L (S n) _) = abort (emp n)
      back (¬□L (S n) _) = abort (emp n)

      back1 : (◇ A ⊃ ⊥) at w :: Γ ⇒ □ (A ⊃ ⊥) [ w ] → Decide¬A-InCPL Γ A w
      back1 (⊃L Z D _) = back D
      back1 (⊃L (S n) _ _) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇L (S n) _) = abort (emp n)
      back1 (□R D) = Inl (λ ω → wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω))
      back1 (□L (S n) _) = abort (emp n)
      back1 (¬◇L (S n) _) = abort (emp n)
      back1 (¬□L (S n) _) = abort (emp n)
       
      back2 : Γ ⇒ ¬ (◇ A) ⊃ □ (¬ A) [ w ] → Decide¬A-InCPL Γ A w
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n)

   demorgan4 : ∀{Γ A w} → Con Γ w → Γ ⇒ □ (¬ A) ⊃ ¬ (◇ A) [ w ]
   demorgan4 con = ⊃R (⊃R (◇L Z (λ ω D → □L (S Z) 
      λ D₀ → abort (con ω (nd→seq (⊃E 
       (seq→nd (wk (⊆to/irrev (≺⊀ ω) (⊆to/irrev (≺⊀ ω) (⊆to/refl _))) 
        (D₀ ω))) 
       (seq→nd (wk (⊆to/irrev (≺⊀ ω) (⊆to/irrev (≺⊀ ω) (⊆to/refl _))) 
        D))))))))
