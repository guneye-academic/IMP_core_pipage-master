A sample file is provided "collegemsg.im"
First 4 lines are ignored in the sample file. Directly starts reading the network.
The file format can be:
node1ID node2ID
ex:
0 1
0 2
1 2

or if you have your own arc weights
node1ID node2ID prob
ex:
0 1 0.25
0 2 0.33
1 2 0.10

To enable arc_weights in the code change Line 372 (2 nd line in intialize_sinan() function )
int arc_weights_ON = 1; (it is 0 default)

If delimeter is not space or tab, correct it in the initalization this function as well. (between Lines 400-420)


