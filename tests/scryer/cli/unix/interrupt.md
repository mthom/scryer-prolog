#```trycmd
#$ scryer-prolog -f --no-add-history -g 'assertz((foo :- foo)),write(ready),nl, catch(foo,_,write(ok)), halt.' & #PID=$!; (sleep 30; kill -INT $PID; sleep 30; kill -9 $PID) & fg 1
#ready
#ok
#```