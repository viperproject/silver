This plugin adds basic (and experimental) support for the verification language Silver as well as the verifiers Silicon and Carbon in Eclipse.

To install, perform the following steps:

0. Install Carbon and/or Silicon from https://bitbucket.org/viperproject/ as well as the necessary prerequisites (e.g. Z3 and Boogie).

1. Download and unzip the current version (Mars) of Eclipse IDE for Java and DSL Developers from http://www.eclipse.org/downloads/.

2. Start Eclipse. Click Help -> Install New Software. Create a new update site by clicking Add... -> Local and selecting the folder that contains this README, and give it a name. 

3. Install the "Viper SDK Feature" from this new update site and restart Eclipse.

4. In the preferences (Window -> Preferences), in the category Viper, enter the paths for the tools you intend to use and their prerequisites. The paths for Silicon and Carbon can also be composite expressions (e.g. "java -jar /path/to/SomeJar.jar") or anything else that results in the start of Silicon/Carbon from the command line.

5. Create a new project. Create a new file in the project and give it a name with the file extension ".sil". If Eclipse asks you if you want to add the Xtext nature to the project, answer yes.

6. An editor should open that has some basic syntax highlighting and error recognition for the Silver language. It also provides basic content assist (press CTRL and space) and linking (e.g. press CTRL and click on a reference to a variable/parameter and you will be directed to its declaration).

7. To run Silicon or Carbon, right click on the file and select Run As -> Verify with Carbon or Verify with Silicon. The result will be shown on the console, and in many cases, errors will be highlighted in the editor itself.
