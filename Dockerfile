FROM python:3.11-slim

WORKDIR /app

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PORT=4000 \
    SIG_CASINO_DB_PATH=/app/data/sig_casino.db

COPY requirements.txt /app/
RUN pip install --no-cache-dir -r requirements.txt

COPY . /app/
RUN mkdir -p /app/data

EXPOSE 4000

CMD ["gunicorn", "-w", "1", "--threads", "8", "--timeout", "60", "-b", "0.0.0.0:4000", "gregmorn_callback_api:app"]
