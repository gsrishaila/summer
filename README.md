# Flowdroid SuperCFG Project
Flowdroid requires jre 1.8 to work correctly
Some kinds of eclipse versions do not support jre 1.8. I have used eclipse oxygen to run flowdroid.

The easiest way of building is to import all the following respective projects into Eclipse. 
-heroes
-jasmin
-soot
-soot-infoflow
-soot-infoflow-android

To get the superCFG, I have modified some files they are

-Test.java          [flowdroid2/soot-infoflow-android-develop/src/soot/jimple/infoflow/android/TestApps/Test.java]
 You can modify the appPath string in line 519 to point to the directory of the apk file. Then run the program. The supergraph will be 
 named dummymain333.dot.

-BlockGraph.java    [flowdroid2/soot-develop/src/soot/toolkits/graph]
-HashChain.java     [flowdroid2/soot-develop/classes/soot/util]


