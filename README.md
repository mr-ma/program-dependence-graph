# program-dependence-graph

Builds full program dependence graph using different pointer analyzers 


#Labeling pass:
```
opt-7 -load build/libpdg.so -reg2mem -pdg-csv -append -relations "relations.csv" -blocks "blocks.csv" $bc
```
