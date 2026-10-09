# Disclosure

JD Jones directed this project. Claude (Anthropic) was used throughout: the computations, the
proofs, the searches, the checkers and the repository were produced in that process, and the
repository was written by Claude. The 7-vertex tournament was found by a vertex-deletion search
inside the Paley tournament on 23 vertices; the exact square value, the rank certificates and the
census of tournaments on at most seven vertices were computed with CP-SAT, CaDiCaL and plain
Python, each result by at least two independent programs, and the travelling checks are the
standard-library certificates under `note/certificates/`. Verification status is stated in
VERIFICATION.md. No independent human review or source-author endorsement is claimed.
