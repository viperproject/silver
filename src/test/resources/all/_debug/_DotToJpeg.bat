DEL *.jpeg
FOR %%A IN (*.dot) DO dot -Tjpeg -O %%A
DEL *.dot