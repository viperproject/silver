import glob

skipTest = "//:: IgnoreFile(/Silver/issue/125/)"

testPaths = glob.glob("./**/*.vpr", recursive=True) + glob.glob("./**/*.sil", recursive=True)

for path in testPaths:
	f = open(path, "r")
	content = f.read()
	f.close()
	if "--*" in content:
		src=open(path,"w")
		src.write(skipTest + "\n" + content)
		src.close()
		print(path)

