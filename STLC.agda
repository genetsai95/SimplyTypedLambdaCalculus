module STLC where

open import Prelude public

-- Types and Terms of STLC
open import STLC.Base public
open import STLC.TermEquationalReasonings public


-- renaming
open import STLC.Renaming public

-- substitution
open import STLC.Substitution public

-- other lemmas about substituions and renamings
open import STLC.Lemmas public

-- judgemental equality
open import STLC.JudgementalEquality public