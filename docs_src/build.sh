for i in `ls *.md` 
do 
	pandoc -t html --filter ./pandocfilter-pygments $i --template template.html -o ../docs/"${i%.md}.html"
done
