-- Constructive Provability Logic 
-- The intuitionistic, modal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Classical definition of modal operators in terms of the others

module IntuitionisticCPL.Classical where
open import Prelude hiding (⊥ ; ¬)
open import Accessibility.Inductive
open import Accessibility.IndexedList
open import IntuitionisticCPL.Core
open import IntuitionisticCPL.Sequent
open import IntuitionisticCPL.Equiv
open import IntuitionisticCPL.Hilbert

module CLASSICAL (UWF : UpwardsWellFounded) where
   open TRANS-UWF UWF
   open PROPERTIES UWF
   open ILIST UWF
   open CORE UWF 
   open SEQUENT UWF
   open EQUIV UWF

   □n : ∀{Γ A w} 
            → Empty Γ w
            → Equiv (DecideA Γ A w) (Γ ⇒ ¬ (□ A) ⊃ ¬□ A [ w ])
   □n {Γ} {A} {w} emp = forward , back2
    where
      forward : (DecideA Γ A w) → (Γ ⇒ ¬ (□ A) ⊃ ¬□ A [ w ])
      forward (Inl D) = ⊃R (⊃L Z 
         (□R (λ ω → wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (D ω))) (⊥L Z))
      forward (Inr (w₀ , ω , DV)) = 
         ⊃R (¬□R ω (λ D → DV (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D)))

      back : (□ A ⊃ ⊥) at w :: Γ ⇒ □ A [ w ] → (DecideA Γ A w)
      back (⊃L Z y' y0) = back y'
      back (⊃L (S n) y' y0) = abort (emp n)
      back (⊥L (S n)) = abort (emp n)
      back (◇L (S n) y') = abort (emp n)
      back (□R D) = Inl (λ ω → wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω))
      back (□L (S n) y') = abort (emp n)
      back (¬◇L (S n) y') = abort (emp n)
      back (¬□L (S n) y') = abort (emp n) 

      back1 : (□ A ⊃ ⊥) at w :: Γ ⇒ ¬□ A [ w ] → (DecideA Γ A w)
      back1 (⊃L Z y' y0) = back y'
      back1 (⊃L (S n) y' y0) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇L (S n) y') = abort (emp n)
      back1 (□L (S n) y') = abort (emp n)
      back1 (¬◇L (S n) y') = abort (emp n)
      back1 (¬□R ω D) = Inr (_ , (ω , 
         λ D₀ → D (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D₀)))
      back1 (¬□L (S n) y') = abort (emp n) 

      back2 : (Γ ⇒ ¬ (□ A) ⊃ ¬□ A [ w ]) → (DecideA Γ A w)
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n) 

   ◇n : ∀{Γ A w}
            → Empty Γ w
            → Equiv (Decide¬A Γ A w) (Γ ⇒ ¬ (◇ A) ⊃ ¬◇ A [ w ])
   ◇n {Γ} {A} {w} emp = forward , back2
    where
      forward : (Decide¬A Γ A w) → (Γ ⇒ ¬ (◇ A) ⊃ ¬◇ A [ w ])
      forward (Inl D) = ⊃R (¬◇R (λ ω E → D ω (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) E)))
      forward (Inr (w₀ , ω , D)) = ⊃R (⊃L Z (◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D)) (⊥L Z))


      back : (◇ A ⊃ ⊥) at  w :: Γ ⇒ ◇ A [ w ] → (Decide¬A Γ A w)
      back (⊃L Z D _) = back D
      back (⊃L (S n) y' y0) = abort (emp n)
      back (⊥L (S n)) = abort (emp n)
      back (◇L (S n) y') = abort (emp n)
      back (◇R ω D) = Inr (_ , ω , wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D)
      back (□L (S n) y') = abort (emp n)
      back (¬◇L (S n) y') = abort (emp n)
      back (¬□L (S n) y') = abort (emp n)  


      back1 :  (◇ A ⊃ ⊥) at w :: Γ ⇒ ¬◇ A [ w ] → (Decide¬A Γ A w)
      back1 (⊃L Z D _) = back D
      back1 (⊃L (S n) y' y0) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇L (S n) y') = abort (emp n)
      back1 (□L (S n) y') = abort (emp n)
      back1 (¬◇L (S n) y') = abort (emp n)
      back1 (¬◇R D) = Inl (λ ω E → D ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) E))
      back1 (¬□L (S n) y') = abort (emp n) 

      
      back2 : (Γ ⇒ ¬ (◇ A) ⊃ ¬◇ A [ w ]) → (Decide¬A Γ A w)
      back2 (⊃R D) = back1 D
      back2 (⊃L n y' y0) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n y') = abort (emp n)
      back2 (□L n y') = abort (emp n)
      back2 (¬◇L n y') = abort (emp n)
      back2 (¬□L n y') = abort (emp n) 




   ◇c : ∀{Γ A w} 
            → Empty Γ w
            → Equiv (Decide◇A-InCPL Γ A w) (Γ ⇒ ¬□ (¬ A) ⊃ ◇ A [ w ])

   ◇c {Γ} {A} {w} emp  = forward , back2 
    where
      forward : (Decide◇A-InCPL Γ A w) → (Γ ⇒ ¬□ (¬ A) ⊃ ◇ A [ w ])
      forward (Inl D⊥) = ⊃R (¬□L Z (λ ω D → D⊥ ω (λ D₀ → D (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D₀)) ))
      forward (Inr (w₀ , ω , DV)) = 
         ⊃R (◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) DV))


      back1 : (¬□ (¬ A)) at w :: Γ ⇒ ◇ A [ w ] →  (Decide◇A-InCPL Γ A w)
      back1 (⊃L (S n) _ _) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇R ω D) = Inr (_ , (ω , (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D)))
      back1 (◇L (S n) _) = abort (emp n)
      back1 (□L (S n) _) = abort (emp n)
      back1 (¬◇L (S n) _) = abort (emp n)
      back1 (¬□L Z D) = Inl (λ ω D₀ → D ω (λ D₁ → D₀ (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D₁)))
      back1 (¬□L (S n) _) = abort (emp n)

      back2 : (Γ ⇒ ¬□ (¬ A) ⊃ ◇ A [ w ]) → (Decide◇A-InCPL Γ A w)
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n)

   nameless : ∀{Γ A w} → (Decide¬A-InCPL Γ A w) → Con Γ w  → (Decide¬A Γ A w)
   nameless (Inl D) con = Inl (λ ω D₀ → con ω (nd→seq (⊃E (seq→nd (D ω)) (seq→nd D₀))))
   nameless (Inr E) con = Inr E 

   ◇d : ∀{Γ A w} 
            → Empty Γ w
            → Equiv (Decide¬A-InCPL Γ A w) (Γ ⇒  ¬ (□ (¬ A)) ⊃ ◇ A [ w ])
   ◇d {Γ} {A} {w} emp = forward , back2
    where 
      forward : (Decide¬A-InCPL Γ A w) → (Γ ⇒  ¬ (□ (¬ A)) ⊃ ◇ A [ w ])
      forward (Inl D) = ⊃R (⊃L Z (□R (λ ω → wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (D ω))) (⊥L Z))
      forward (Inr (w₀ , ω , D)) = ⊃R (◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D))

      back : (□ (A ⊃ ⊥) ⊃ ⊥) at w :: Γ ⇒ □ (A ⊃ ⊥) [ w ] → (Decide¬A-InCPL Γ A w)
      back (⊃L Z D E) = back D
      back (⊃L (S n) _ _) = abort (emp n)
      back (⊥L (S n)) = abort (emp n)
      back (◇L (S n) _) = abort (emp n)
      back (□R D) = Inl (λ ω → wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω))
      back (□L (S n) _) = abort (emp n)
      back (¬◇L (S n) _) = abort (emp n)
      back (¬□L (S n) _) = abort (emp n)


      back1 : (□ (A ⊃ ⊥) ⊃ ⊥) at w :: Γ ⇒ ◇ A [ w ] → (Decide¬A-InCPL Γ A w)
      back1 (⊃L Z D E) = back D
      back1 (⊃L (S n) _ _) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇R ω D) = Inr (_ , (ω , (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D)))
      back1 (◇L (S n) _) = abort (emp n)
      back1 (□L (S n) _) = abort (emp n)
      back1 (¬◇L (S n) _) = abort (emp n)
      back1 (¬□L (S n) _) = abort (emp n)

      back2 : (Γ ⇒  ¬ (□ (¬ A)) ⊃ ◇ A [ w ]) → (Decide¬A-InCPL Γ A w)
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n)

   □d : ∀{Γ A w} 
            → Empty Γ w
            → Equiv (DecideA-InCPL Γ A w) (Γ ⇒  ¬ (◇ (¬ A)) ⊃ □ A [ w ])
   □d {Γ} {A} {w} emp = forward , back2
    where
      forward : (DecideA-InCPL Γ A w) → (Γ ⇒  ¬ (◇ (¬ A)) ⊃ □ A [ w ])
      forward (Inl inl) = ⊃R (□R (λ ω → wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) (inl ω)))
      forward (Inr (w₀ , ω , D)) = ⊃R (⊃L Z (◇R ω (wk (⊆to/wkenirrev (≺⊀ ω) (⊆to/refl _)) D)) (⊥L Z)) 
     
      back : (◇ (A ⊃ ⊥) ⊃ ⊥) at w :: Γ ⇒ ◇ (A ⊃ ⊥) [ w ] → (DecideA-InCPL Γ A w)
      back (⊃L Z D _) = back D
      back (⊃L (S n) _ _) = abort (emp n)
      back (⊥L (S n)) = abort (emp n)
      back (◇R ω D) = Inr (_ , ω , (wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) D))
      back (◇L (S n) _) = abort (emp n)
      back (□L (S n) _) = abort (emp n)
      back (¬◇L (S n) _) = abort (emp n)
      back (¬□L (S n) _) = abort (emp n)

      back1 : (◇ (A ⊃ ⊥) ⊃ ⊥) at w :: Γ ⇒ □ A [ w ] → (DecideA-InCPL Γ A w)
      back1 (⊃L Z D _) = back D
      back1 (⊃L (S n) _ _) = abort (emp n)
      back1 (⊥L (S n)) = abort (emp n)
      back1 (◇L (S n) y') = abort (emp n)
      back1 (□R D) = Inl (λ ω → wk (⊆to/irrev (≺⊀ ω) (⊆to/refl _)) (D ω))
      back1 (□L (S n) y') = abort (emp n)
      back1 (¬◇L (S n) y') = abort (emp n)
      back1 (¬□L (S n) y') = abort (emp n)

      back2 : (Γ ⇒  ¬ (◇ (¬ A)) ⊃ □ A [ w ]) → (DecideA-InCPL Γ A w)
      back2 (⊃R D) = back1 D
      back2 (⊃L n _ _) = abort (emp n)
      back2 (⊥L n) = abort (emp n)
      back2 (◇L n _) = abort (emp n)
      back2 (□L n _) = abort (emp n)
      back2 (¬◇L n _) = abort (emp n)
      back2 (¬□L n _) = abort (emp n) 