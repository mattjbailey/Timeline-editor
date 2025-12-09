import os
import json
import datetime

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    # Target next to gui.py in timeline package
    timeline_dir = os.path.join(os.path.dirname(here), 'timeline')
    os.makedirs(timeline_dir, exist_ok=True)
    target = os.path.join(timeline_dir, 'build_info.json')
    info = {
        'build_time': datetime.datetime.utcnow().isoformat() + 'Z'
    }
    with open(target, 'w', encoding='utf-8') as f:
        json.dump(info, f, indent=2)
    print(f'Wrote {target}')

if __name__ == '__main__':
    main()