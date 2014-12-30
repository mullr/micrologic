#!/bin/sh
emacs -eval '(progn (find-file "literate.org") (org-html-export-to-html))' -kill
git co gh-pages

rm -f index.md
echo "---" >> index.md
echo "layout: index" >> index.md
echo "---" >> index.md
git show master:README.md >> index.md

git add index.md
git add literate.html
git commit -m "Update docs"

git co master
