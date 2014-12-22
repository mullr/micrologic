lein marg
git co gh-pages

rm index.md
echo "---" >> index.md
echo "layout: index" >> index.md
echo "---" >> index.md
git show master:README.md >> index.md

mv docs/uberdoc.html literate.html

git add index.md
git add literate.html
git commit -m "Update docs"

git co master
