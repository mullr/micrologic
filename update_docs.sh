#!/bin/sh
emacs -eval "(progn (load-theme 'spacemacs-light) (find-file \"literate.org\") (org-html-export-to-html))" -kill
mv literate.html new.html

git co gh-pages

mv new.html literate.html

rm -f index.md
echo "---" >> index.md
echo "layout: index" >> index.md
echo "---" >> index.md
git show master:README.md >> index.md

git add index.md
git add literate.html
git commit -m "Update docs"

git co master
