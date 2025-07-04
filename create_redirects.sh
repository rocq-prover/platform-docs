#!/usr/bin/env bash
# filepath: create_redirects.sh

# List of old and new paths (old_path new_path)
redirects=(
  "Tutorial_Equations_basics.html equations/tutorial_basics.html"
  "Tutorial_Equations_indexed.html equations/tutorial_indexed.html"
  "Tutorial_Equations_Obligations.html equations/tutorial_obligations.html"
  "Tutorial_Equations_wf.html equations/tutorial_wf_recursion.html"
  "RequireImportTutorial.html features/tutorial_require_import.html"
  "SearchTutorial.html features/tutorial_search_for_lemma.html"
  "Tutorial_hierarchy_builder.html hierarchy_builder/tutorial_basics.html"
  "How_to_contradiction.html metaprogramming/ltac2/how_to_contradiction.html"
  "Tutorial_Ltac2_backtracking.html metaprogramming/ltac2/tutorial_backtracking.html"
  "Tutorial_Ltac2_matching_terms_and_goals.html metaprogramming/ltac2/tutorial_matching_terms_and_goals.html"
  "Tutorial_Ltac2_types_and_thunking.html metaprogramming/ltac2/tutorial_types_and_thunking.html"
  "Explanation_Bidirectionality_Hints.html rocq_theory/explanation_bidirectionality_hints.html"
  "Explanation_Template_Polymorphism.html rocq_theory/explanation_template_polymorphism.html"
  "Tutorial_Chaining_Tactics.html writing_proofs/tutorial_chaining_tactics.html"
  "Tutorial_intro_patterns.html writing_proofs/tutorial_intro_patterns.html"
)

for entry in "${redirects[@]}"; do
  old_path=$(echo "$entry" | awk '{print $1}')
  new_path=$(echo "$entry" | awk '{print $2}')
  dir=$(dirname "$old_path")
  mkdir -p "$dir"
  cat > "$old_path" <<EOF
<!DOCTYPE html>
<html>
  <head>
    <meta http-equiv="refresh" content="0; url=$new_path" />
    <link rel="canonical" href="$new_path" />
    <title>Redirecting...</title>
  </head>
  <body>
    <p>Redirecting to <a href="$new_path">$new_path</a></p>
  </body>
</html>
EOF
  echo "Created redirect: $old_path → $new_path"
done