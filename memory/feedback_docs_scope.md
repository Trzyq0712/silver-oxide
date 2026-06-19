---
name: feedback-docs-scope
description: When documenting architecture in CLAUDE.md, drop speculative implementation details that haven't been decided yet; document only settled design.
metadata:
  type: feedback
---

When writing or updating architecture documentation (CLAUDE.md and similar), document only what's actually decided. Do not include speculative implementation strategies — particularly verifier internals (push/pop strategies, ITE hoisting, goal destructuring, etc.) — until they've been settled.

**Why:** User rejected a plan that included two pillars about verifier implementation ("Linear Push/Pop Verifier Loop" and "Goal Destructuring & ITE Hoisting") with the note: "For now we can skip on how exactly we will implement the verifier. Drop points 4 and 5 from the context." Documenting unsettled design pollutes CLAUDE.md and constrains future decisions.

**How to apply:** When asked to incorporate a discussion into the architecture docs, separate (a) settled design rules from (b) implementation strategy speculation. Write only (a). For (b), either omit entirely or add a short "out of scope — to be settled when the backend lands" note. When in doubt, ask the user which items are firm.
