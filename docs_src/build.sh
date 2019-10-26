for i in `ls *.md` 
do 
	pandoc -t html -f markdown-tex_math_dollars-raw_tex --filter ./pandocfilter-pygments $i --template template.html -o ../docs/"${i%.md}.html"
done
