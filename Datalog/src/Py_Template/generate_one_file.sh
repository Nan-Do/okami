#! /bin/sh

# Copy the header of the file
echo "#! /usr/bin/python" > solver-py.py
head -n 5 solver.py >> solver-py.py

echo "import sys" >> solver-py.py
echo "" >> solver-py.py
echo "from array import array" >> solver-py.py
echo "from collections import deque, namedtuple" >> solver-py.py

# utils.py
tail -n +8 utils.py  >> solver-py.py

# datastructure.py
tail -n +8 datastructure.py  >> solver-py.py

# solver.py
tail -n +13 solver.py >> solver-py.py

# main.py
tail -n +11 main.py >> solver-py.py

chmod +x solver-py.py
