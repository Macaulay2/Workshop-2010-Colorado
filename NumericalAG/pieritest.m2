restart
needs "pieriHom.m2"

M = skewSchubertVariety((3,7),{2,1,0},{1,1,0})
launchSimpleSchubert((3,7),{2,1,0},{1,1,0})
peek H	
H#({2,1,0},{1,1,0})


M = skewSchubertVariety((2,4),{1,0},{1,0})
launchSimpleSchubert((2,4),{1,0},{1,0})
H#({1,0},{1,0})
