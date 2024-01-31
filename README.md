# Simply Typed λ-Calculus
This is a practice project that formulates *STλC* with
- unit type
- answer type (boolean type)
- product type
- function type
in Agda.  

This *STλC* contains
- syntax for terms and types (de-Bruijn-indexed)
- renaming, substitution, and lemmas about them
- reductions and conversions
- definitions of neutral and normal forms

In addition, the project proves some basic properties about *STλC* including
- consistency: $\Gamma\not\vdash{\sf yes}={\sf no}:{\sf Ans}$
- canonicity: For every term $\vdash t:{\sf Ans}$, either $\vdash t\equiv{\sf yes}:{\sf Ans}$ or $\vdash t\equiv{\sf no}:{\sf Ans}$.
- normalization: Every term can be normalized.
  
The method used to prove the properties above refers to:
> <cite>Huang, X. (2023, October 3). Synthetic Tait Computability the Hard Way. arXiv.Org. https://arxiv.org/abs/2310.02051v1 </cite>
